/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Assembly
import VaughtConjecture.Continuation.ReadingLayerBand

/-!
# Dominating donor tops fail at every donor coface over a forced top (work file for `h3`)

Work file (placement later).  Compiled in this repository (theorem named):

* **No donor coface has dominating tops** (`H3.not_donorTopsDominate`): let the coface `d` of the
  root force a new top `y` below a root cell `z` (every lawful labelling of `d` is at `y` at most
  its value at `z`), and let the coatom face `p` carry a lawful labelling `wP` with the bottoms of
  its label, at least a label `c ≠ ⊥` self-visible at `k + 1` off them, strictly below a cell `a`
  of grade at least the grade `N` of the cap at `z`.  Then for **every** coface `tb` of `p` with
  face `d` and every grade `k'` with `grade a ≤ k'`, the tops of the donor do not dominate the
  common face (`H3.DonorTopsDominate` fails): the capped lift of `tb` from `p` at `c`, relative to
  the collapse of `tb.label` to `c` (`StageType.exists_isLawful_raise`), is `wP` on `p`, in the
  class, and at `y` at most `wP z < wP a`.
* **The domination conjunct of `H3.exists_raiseCoface` fails there**
  (`H3.not_exists_raiseCoface_dominate`).  This refutes the domination conjunct for every legal
  donor coface at such a context; it says nothing about (R3) or about the class route as a whole.
* **The forced top needs a root top** (`H3.label_eq_top_of_forced`): the hypothesis on `d` holds
  only at a root cell labelled `⊤`, so it has no instance at the apex contexts compiled so far
  (`StageType.markedCapContextBelow'_addApex` asks the root labels to avoid `⊤`).
* **Apex contexts with root tops** (`StageType.markedCapContextBelow'_addApex_of_top`): that
  condition is not needed; the apex reads every cell labelled `⊤` at the code of `⊤`, fixed by the
  replacement at the grade of the apex.  So acquired contexts with root cells labelled `⊤` exist.
* **At a cap of the top grade the tops dominate** (`H3.donorTopsDominate_of_lt`): the common face
  has no cell of grade at least the cap.  So the hypothesis of `H3.not_donorTopsDominate` on `p`
  needs a cap below the top grade; the apex contexts have their cap at the top grade.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower StageType

namespace H3

variable {α : Ordinal.{u}} {n k : ℕ}

section Dominate

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {t : StageType.{u} α n} (hpt : restrictFace g p = some t)
  {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)
  (htbd : restrictFace (extendByLast g) tb = some d)

/-- **No donor coface has dominating tops over a forced top.** -/
theorem not_donorTopsDominate {c r : Fin t'.card} (hc : 0 < t'.toCellScheme.grade c)
    {j₀ : Fin d.card} (hj₀ : d.label j₀ = ⊤) (hj₀l : Fin.last n ∈ d.toCellScheme.scope j₀)
    {z₀ : Fin t.card}
    (hforce : ∀ v : Fin d.card → Label.{u}, d.rows.IsLawful v → v j₀ ≤ v (faceCell hd.2 z₀))
    {a₀ : Fin p.card} {k' : ℕ} (haN : t'.toCellScheme.grade c ≤ p.toCellScheme.grade a₀)
    (hak : p.toCellScheme.grade a₀ ≤ k') (hk' : k' ≤ k + 1)
    {cc : Label.{u}} (hcc : IsSelfVisible (k + 1) cc) (hccb : cc ≠ ⊥)
    {wP : Fin p.card → Label.{u}} (hwP : p.rows.IsLawful wP)
    (hwPbot : ∀ i, wP i = ⊥ ↔ p.label i = ⊥) (hwPc : ∀ i, p.label i ≠ ⊥ → cc ≤ wP i)
    (hsep : wP (faceCell hpt z₀) < wP a₀) :
    ¬ DonorTopsDominate (requests ht' hp htb htbd c r hc) (classCells ht' hp htb htbd)
      (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  classical
  intro hdom
  have hL := restrictFace_left_seed ht' hp htb
  have hR : restrictFace (Coatom.right k) (seed ht' hp htb).amalgam = some tb :=
    (seed ht' hp htb).restrictFace_right
  have hA := restrictFace_donor_seed ht' hp htb htbd
  -- the capped lift of `tb` from `p` at `cc`, relative to the collapse of its label
  have hΦ := isWitness_bandCollapse (K := k + 1) hcc hccb
  obtain ⟨v, hv, hvP, hvc⟩ := exists_isLawful_raise htb.1 htb.2 hwP le_rfl hΦ
    (fun z h ↦ eq_bot_of_bandCollapse_eq_bot hccb h) hcc fun i ↦ by
      by_cases hb : p.label i = ⊥
      · rw [hb, bandCollapse_bot, (hwPbot i).mpr hb]
      · rw [min_eq_right (hwPc i hb)]
        by_cases ht : p.label i = ⊤
        · rw [ht, bandCollapse_top, min_eq_right le_top]
        · rw [bandCollapse_of_ne hb ht, min_self]
  have hvne (y : Fin tb.card) (hy : tb.label y ≠ ⊥) : v y ≠ ⊥ := fun h ↦ by
    have e := hvc y
    rw [h, min_bot_left] at e
    have hΦy : bandCollapse cc (tb.label y) ≠ ⊥ :=
      fun h' ↦ hy (eq_bot_of_bandCollapse_eq_bot hccb h')
    exact (min_eq_bot.mp e.symm).elim hΦy hccb
  set f : Prof (seed ht' hp htb) := faceExtend hR v
  have hfR (y : Fin tb.card) : f (faceCell hR y) = v y := faceExtend_faceCell hR v y
  -- `f` is lawful below the donor coatom
  have hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow
      (univ.erase (Fin.castSucc (Fin.last k)), k') fun e ↦ f e := by
    have h := isLawfulBelow_of_faceCell hR (x := f)
      (by simpa only [f, faceExtend_faceCell] using hv)
    rw [Coatom.univ_map_right] at h
    exact h.mono (Prod.mk_le_mk.mpr ⟨le_rfl, hk'⟩)
  -- `f` is in the class
  have hfB : ∀ e ∈ classCells ht' hp htb htbd, f e ≠ ⊥ := by
    intro e he
    have hvis : e ∈ (seed ht' hp htb).amalgam.toScheme.visibleCells (Coatom.right k) := by
      rw [Scheme.mem_visibleCells]
      intro z hz
      rcases he with ⟨x, hxv, -, rfl⟩ | ⟨j, -, -, rfl⟩
      · rw [scope_faceCell] at hz
        obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
        obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp hxv hw
        refine ⟨Fin.castSucc (g i), ?_⟩
        rw [← hi]
        simp [Coatom.right]
      · rw [scope_faceCell] at hz
        obtain ⟨w, -, rfl⟩ := mem_map.mp hz
        refine ⟨extendByLast g w, ?_⟩
        rw [Coatom.right, ← Function.Embedding.trans_apply, extendByLast_trans]
    obtain ⟨y, rfl⟩ := exists_faceCell_eq hR hvis
    rw [hfR]
    refine hvne y fun hy ↦ ?_
    have hlab : (seed ht' hp htb).amalgam.label (faceCell hR y) ≠ ⊥ := by
      rcases he with ⟨x, -, hx, hxe⟩ | ⟨j, hj, -, hje⟩
      · rw [hxe, label_faceCell]; exact hx
      · rw [hje, label_faceCell, hj]; exact top_ne_bot
    rw [label_faceCell] at hlab
    exact hlab hy
  obtain ⟨h, -, hah, hhy⟩ := hdom f hf hfB
  -- the cell `a` of the common face
  have hpcR : faceCell hL (faceCell hp a₀) = faceCell hR (faceCell htb.2 a₀) :=
    faceCell_faceCell (h := Fin.castSuccEmb) hL hR hp htb.2 a₀
  have ha := hah (faceCell hR (faceCell htb.2 a₀)) ?_ ?_ ?_
  rotate_left
  · refine ⟨?_, ?_⟩
    · change (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hR (faceCell htb.2 a₀)) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_right]
      exact map_subset_map.mpr (subset_univ _)
    · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hR (faceCell htb.2 a₀)) ≤ k'
      rw [grade_faceCell, grade_faceCell]
      exact hak
  · rw [← hpcR, scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤ _
    rw [grade_faceCell, grade_faceCell, grade_faceCell]
    exact haN
  rw [hfR, hvP] at ha
  -- the new top `y`
  have hyT : faceCell hA j₀ ∈ (requests ht' hp htb htbd c r hc).T := ⟨j₀, hj₀, hj₀l, rfl⟩
  have hy := hhy _ hyT
  rw [faceCell_trans (extendByLast_trans g Fin.castSuccEmb) hR htbd hA j₀, hfR] at hy
  have hvd := hforce _ (isLawful_comp_faceCell htbd hv)
  rw [← faceCell_faceCell (h := g) htb.2 htbd hpt hd.2 z₀, hvP] at hvd
  exact absurd (ha.trans (hy.trans hvd)) (not_le.mpr hsep)

/-- **The domination conjunct of `H3.exists_raiseCoface` fails over a forced top**: under the
hypotheses of `H3.not_donorTopsDominate` on `d` and `p`, no coface `tb` of `p` with face `d` has
dominating tops at every grade from the grade of the cap (at the grade `k + 1`). -/
theorem not_exists_raiseCoface_dominate {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) {g : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    {j₀ : Fin d.card} (hj₀ : d.label j₀ = ⊤) (hj₀l : Fin.last n ∈ d.toCellScheme.scope j₀)
    {z₀ : Fin t.card}
    (hforce : ∀ v : Fin d.card → Label.{u}, d.rows.IsLawful v → v j₀ ≤ v (faceCell hd.2 z₀))
    {a₀ : Fin p.card} (haN : t'.toCellScheme.grade c ≤ p.toCellScheme.grade a₀)
    {cc : Label.{u}} (hcc : IsSelfVisible (k + 1) cc) (hccb : cc ≠ ⊥)
    {wP : Fin p.card → Label.{u}} (hwP : p.rows.IsLawful wP)
    (hwPbot : ∀ i, wP i = ⊥ ↔ p.label i = ⊥) (hwPc : ∀ i, p.label i ≠ ⊥ → cc ≤ wP i)
    (hsep : wP (faceCell ((restrictFace_trans t' _ g hp).trans ht) z₀) < wP a₀) :
    ¬ ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        DonorTopsDominate (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  rintro ⟨tb, htb, htbd, hdom⟩
  have hpt : restrictFace g p = some t := (restrictFace_trans t' _ g hp).trans ht
  have hak : p.toCellScheme.grade a₀ ≤ k + 1 := (p.grade_le a₀).trans (Nat.le_succ k)
  exact not_donorTopsDominate ht' hp htb hpt hd htbd (r := r) _ hj₀ hj₀l hforce haN hak le_rfl
    hcc hccb hwP hwPbot hwPc hsep (hdom (k + 1) (haN.trans hak) le_rfl)

/-- **At a cap of the top grade the tops dominate** (with `h = ⊥`): the cells of the common face
have grade at most `k`, below the grade of the cap, so there is nothing to dominate. -/
theorem donorTopsDominate_of_lt {c r : Fin t'.card} (hc : 0 < t'.toCellScheme.grade c)
    (hkN : k < t'.toCellScheme.grade c) (B : Set (Fin (seed ht' hp htb).amalgam.card))
    (k' : ℕ) :
    DonorTopsDominate (requests ht' hp htb htbd c r hc) B (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) k' := by
  intro f _ _
  refine ⟨⊥, isSelfVisible_bot _, fun e he hC hN ↦ absurd hN (not_le.mpr ?_),
    fun _ _ ↦ bot_le⟩
  have h1 := (seed ht' hp htb).amalgam.isWellFormed.isWellFormed.grade_le_card e
  have hsub : (seed ht' hp htb).amalgam.toCellScheme.scope e ⊆
      (univ.erase (Fin.last (k + 1))).erase (Fin.castSucc (Fin.last k)) := fun z hz ↦
    mem_erase.mpr ⟨(mem_erase.mp (he.1 hz)).1, hC hz⟩
  have h2 := card_le_card hsub
  rw [card_erase_of_mem (mem_erase.mpr ⟨Seed.last_ne_castSucc.symm, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
  change _ < (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell
    (restrictFace_left_seed ht' hp htb) c)
  rw [grade_faceCell]
  omega

end Dominate

/-- **A forced top lies below a root cell labelled `⊤`**: if every lawful labelling of `d` is at
the cell `j₀` labelled `⊤` at most its value at the root cell `z₀`, then `z₀` is labelled `⊤` (the
label of `d` is lawful).  So the hypothesis of `H3.not_donorTopsDominate` on `d` needs a root cell
labelled `⊤`; the apex contexts of `StageType.markedCapContextBelow'_addApex` have none. -/
theorem label_eq_top_of_forced {t : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hdt : restrictFace Fin.castSuccEmb d = some t) {j₀ : Fin d.card} (hj₀ : d.label j₀ = ⊤)
    {z₀ : Fin t.card}
    (hforce : ∀ v : Fin d.card → Label.{u}, d.rows.IsLawful v → v j₀ ≤ v (faceCell hdt z₀)) :
    t.label z₀ = ⊤ := by
  have h := hforce d.label d.isLawful
  rw [hj₀, label_faceCell] at h
  exact top_le_iff.mp h

end H3

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- The code of the formal top is fixed by every replacement at the threshold `k`. -/
theorem visibilityReplace_blockTopCode (V : Finset Label.{u}) {i : ℕ} :
    visibilityReplace k i ((Label.blockTopCode V k : Ordinal.{u}) : Label.{u}) =
      (Label.blockTopCode V k : Label.{u}) := by
  unfold Label.blockTopCode
  rw [Label.visibilityReplace_block]
  simp

/-- **An apex type is a context respecting the root bottoms, root tops allowed**: the statement of
`StageType.markedCapContextBelow'_addApex` without the condition that the root labels avoid `⊤`.
The apex is the cap and the marker; it reads every cell labelled `⊤` at the code of `⊤`, whose
finite part is the grade `k` of the apex, so the replacement at `k` fixes it. -/
theorem markedCapContextBelow'_addApex_of_top {t₀ : StageType.{u} α k}
    (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k) {h : Fin n ↪ Fin k} (hnk : n + 1 < k)
    (hoff : ∀ y ∈ (t₀.addApex ht₀ hk).visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ),
      Order.IsSuccPrelimit μ → (t₀.addApex ht₀ hk).label y = ((μ + f : Ordinal.{u}) : Label.{u}) →
        f < k) :
    TiedRootCapRelabel.MarkedCapContextBelow' (t₀.addApex ht₀ hk) h := by
  have hg : (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _) = k :=
    congrArg Prod.snd (addApex_gradedIndex_last ht₀ hk)
  refine ⟨Fin.last _, Fin.last _, ⟨⟨addApex_scope_last ht₀ hk, addApex_label_last ht₀ hk,
    fun x _ ↦ by rw [hg]; exact (t₀.addApex ht₀ hk).grade_le x⟩,
    ⟨addApex_label_last ht₀ hk, (t₀.addApex ht₀ hk).toCellScheme.mem_below_gradedIndex _,
      fun x hx _ ↦ le_of_eq ((rowAt_addApex_last ht₀ hk _).trans
        ((congrArg (blockEncode (apexCodes ht₀) k) ((addApex_label_last ht₀ hk).trans
          hx.symm)).trans (rowAt_addApex_last ht₀ hk x).symm))⟩,
    by rw [hg]; exact hnk, fun a _ hat ↦ ?_⟩,
    fun y hy μ f hμ hf ↦ by rw [hg]; exact hoff y hy μ f hμ hf,
    fun y _ hyb ↦ (rowAt_addApex_last_eq_bot_iff ht₀ hk y).mpr hyb⟩
  have h1 : (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) (Fin.last _) =
      (Label.blockTopCode (apexCodes ht₀) k : Label.{u}) :=
    (rowAt_addApex_last ht₀ hk _).trans (by rw [addApex_label_last]; rfl)
  have h2 : (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) a =
      (Label.blockTopCode (apexCodes ht₀) k : Label.{u}) :=
    (rowAt_addApex_last ht₀ hk a).trans (by rw [hat]; rfl)
  rw [hg, h1, h2, visibilityReplace_blockTopCode]

end StageType

end VaughtConjecture

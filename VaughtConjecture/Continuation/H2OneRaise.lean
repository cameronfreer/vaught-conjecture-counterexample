/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OneEngine
import VaughtConjecture.Continuation.H2Collapse

/-!
# Top grade `1` at two points: donor raising at grade `1` (work file)

WORK FILE (branch `research/work-twolift`).  Every declaration here is proved.

At grade `1` on two points the capped lift `H2.hasCappedLifts_of_isLegal` (which needs the arity of
the root below the grade) and the witness closure of the lawful labellings of the donor (a witness
bounded by the grade `1` need not keep the labels of the cells of grade `2` self-visible at `2`) are
not available.  Both hold on the **grade-`1` faces** (`H2.LawfulOne`: lawful below `(univ, 1)`, `⊥`
at the cells of grade `2`): the capped lift from the root is bountifulness
(`H2.hasCappedLifts_lawfulOne_one`) and witnesses bounded by `1` keep them (`H2.lawfulOne_map`). So
**donor raising with the gap between the grade-`1` faces holds with no hypothesis beyond the
designation** (`H2.donorRaisingGap_oneFace`), the order law and the frontier bound hold there
(`H2.frontier_le_lawfulOne`), and the clause is an admission of states between the grade-`1` faces
under owner lowering there (`H2.stateAdmission_oneFace`).  The engine of
`VaughtConjecture.Continuation.H2OneEngine` runs on exactly these faces, and
`H2.exists_completion_recProp_one_of_admission` gives the conclusion of
`H2.exists_completion_recProp_one` (on the research branch `research/port-low-padded`) from any such
admission.

Donor raising between the full lawful labellings (`H2.donorRaisingGap_one`) passes through the
extension from `(univ, 1)` to `(univ, 2)` capped at `h`: bountifulness when `h` is self-visible at
`2`, and otherwise (`h` of finite part `1`) the named hypothesis `H2.GradeTwoExtAtOne`.  It is not
needed by the engine.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission Seed CellScheme

variable {α : Ordinal.{u}}

/-! ### The grade-`1` faces of a donor -/

/-- **The extension from grade `1` to grade `2` at the caps of finite part `1`** (a hypothesis on
the donor): at a cap `h` self-visible at `1` and not at `2`, a labelling lawful below `(univ, 1)`
agreeing at the cells of grade `1` with a lawful labelling `R` capped at `h` extends, unchanged
there, to a lawful labelling agreeing with `R` capped at `h`.  At the caps self-visible at `2` this
is bountifulness. -/
def GradeTwoExtAtOne (tb : StageType.{u} α 2) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible 1 h → ¬ IsSelfVisible 2 h →
    ∀ {w R : Fin tb.card → Label.{u}},
      tb.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d) → tb.rows.IsLawful R →
      (∀ d, tb.toCellScheme.grade d ≤ 1 → min (w d) h = min (R d) h) →
      ∃ W, tb.rows.IsLawful W ∧ (∀ d, tb.toCellScheme.grade d ≤ 1 → W d = w d) ∧
        ∀ d, min (W d) h = min (R d) h

variable {p : StageType.{u} α 1} {tb : StageType.{u} α 2}

theorem mem_below_one_iff {d : Fin tb.card} :
    d ∈ tb.toCellScheme.below ((univ : Finset (Fin 2)), 1) ↔ tb.toCellScheme.grade d ≤ 1 :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨subset_univ _, h⟩⟩

/-- **The extension from `(univ, 1)` to `(univ, 2)`**, at a cap self-visible at `2` by
bountifulness, and at a cap of finite part `1` by `H2.GradeTwoExtAtOne`. -/
theorem exists_ext_two (htbleg : tb.IsLegal) (hext : GradeTwoExtAtOne tb) {h : Label.{u}}
    (hh : IsSelfVisible 1 h) {w R : Fin tb.card → Label.{u}}
    (hw : tb.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d))
    (hR : tb.rows.IsLawful R)
    (hwR : ∀ d, tb.toCellScheme.grade d ≤ 1 → min (w d) h = min (R d) h) :
    ∃ W, tb.rows.IsLawful W ∧ (∀ d, tb.toCellScheme.grade d ≤ 1 → W d = w d) ∧
      ∀ d, min (W d) h = min (R d) h := by
  by_cases hh2 : IsSelfVisible 2 h
  swap
  · exact hext hh hh2 hw hR hwR
  have hle : (((univ : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_rfl, by omega⟩
  obtain ⟨q', hq', hq'R, hq'w⟩ := (Rows.cappedLift_iff_forall_exists hle).mp
    (htbleg.isBountiful ⟨tb.univ_mem_faces, one_pos, by simp⟩
      ⟨tb.univ_mem_faces, two_pos, by simp⟩ hle) h hh2 (fun d ↦ w d) (fun d ↦ R d) hw
    (hR.isLawfulBelow _) (fun d ↦ (hwR d d.2.2).symm)
  have hall (d : Fin tb.card) : d ∈ tb.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, tb.grade_le d⟩
  exact ⟨fun d ↦ q' ⟨d, hall d⟩, hq'.isLawful hall, fun d hd ↦ hq'w ⟨d, subset_univ _, hd⟩,
    fun d ↦ hq'R ⟨d, hall d⟩⟩

/-- **The capped lift into the grade-`1` faces**, from the root at grade `1` (bountifulness). -/
theorem hasCappedLifts_lawfulOne {t' : StageType.{u} α 2}
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    HasCappedLifts (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      (LawfulOne tb) := by
  classical
  intro h hh R f hR hf hagr
  have hy := StageType.isLawful_comp_faceCell hp hf
  obtain ⟨hfm, -⟩ := (StageType.restrictFace_eq_some_iff (t := tb) (f := Fin.castSuccEmb)).mp htbp
  have he := StageType.comap_toScheme_of_restrictFace htbp
  have hinj : Function.Injective (StageType.faceCell htbp) := by
    intro i j hij
    have := (tb.toScheme.cellMap Fin.castSuccEmb).injective hij
    exact Fin.cast_injective _ this
  set x : Fin tb.card → Label.{u} := Function.extend (StageType.faceCell htbp)
    (fun i ↦ f (StageType.faceCell hp i)) (fun _ ↦ ⊥)
  have hx (i : Fin p.card) : x (StageType.faceCell htbp i) = f (StageType.faceCell hp i) :=
    hinj.extend_apply _ _ i
  have hpX : tb.rows.IsLawfulBelow
      (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin 1)), 1)) (fun d ↦ x d) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ x).mp ?_
    convert hy.isLawfulBelow ((univ : Finset (Fin 1)), 1) using 2 with i
    exact hx i.1
  have hXY : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin 1)), 1) ≤
      ((univ : Finset (Fin 2)), 1) := ⟨subset_univ _, le_rfl⟩
  have hX : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin 1)), 1) ∈
      tb.toCellScheme.gradedFaces := ⟨hfm, one_pos, by simp⟩
  have hY : ((univ : Finset (Fin 2)), 1) ∈ tb.toCellScheme.gradedFaces :=
    ⟨tb.univ_mem_faces, one_pos, by simp⟩
  have hlift := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (htbleg.isBountiful hX hY hXY) h hh (fun d ↦ x d) (fun d ↦ R d) hpX hR.1 (fun d ↦ ?_)
  rotate_left
  · have hvis : d.1 ∈ tb.toScheme.visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
      have hy' : y ∈ (univ : Finset (Fin 1)).map Fin.castSuccEmb := d.2.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hvis
    change min (R d.1) h = min (x d.1) h
    rw [← hi]
    change min (R (StageType.faceCell htbp i)) h = min (x (StageType.faceCell htbp i)) h
    rw [hx]
    exact (hagr i).symm
  obtain ⟨q', hq', hq'R, hq'p⟩ := hlift
  refine ⟨fun d ↦ if hd : d ∈ tb.toCellScheme.below ((univ : Finset (Fin 2)), 1) then
    q' ⟨d, hd⟩ else ⊥, ⟨?_, fun d hd ↦ dite_eq_right fun h' ↦ hd h'.2⟩, fun i ↦ ?_, fun d ↦ ?_⟩
  · convert hq' using 1
    exact funext fun d ↦ dite_eq_left d.2
  · have hvX : StageType.faceCell htbp i ∈ tb.toCellScheme.below
        (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin 1)), 1)) :=
      (CellScheme.mem_below _).mpr
        ⟨show tb.toCellScheme.scope (StageType.faceCell htbp i) ⊆
            (univ : Finset (Fin 1)).map Fin.castSuccEmb by
          rw [StageType.scope_faceCell]; exact map_subset_map.mpr (subset_univ _),
        show tb.toCellScheme.grade (StageType.faceCell htbp i) ≤ 1 by
          rw [StageType.grade_faceCell]; exact p.grade_le i⟩
    have := hq'p ⟨_, hvX⟩
    refine (dite_eq_left (Set.inclusion (tb.toCellScheme.below_mono hXY) ⟨_, hvX⟩).2).trans ?_
    exact this.trans (hx i)
  · by_cases hd : d ∈ tb.toCellScheme.below ((univ : Finset (Fin 2)), 1)
    · exact (congrArg (min · h) (dite_eq_left hd)).trans (hq'R ⟨d, hd⟩)
    · refine (congrArg (min · h) (dite_eq_right hd)).trans ?_
      rw [hR.2 d fun h' ↦ hd ⟨subset_univ _, h'⟩]

/-- **Witnesses bounded by the grade `1` keep the grade-`1` faces.** -/
theorem lawfulOne_map {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor 1) ν)
    (hle : ∀ x, x ≤ ν x) {W : Fin tb.card → Label.{u}} (hW : LawfulOne tb W) :
    LawfulOne tb (fun d ↦ ν (W d)) := by
  refine ⟨?_, fun d hd ↦ (congrArg ν (hW.2 d hd)).trans hν.map_bot⟩
  exact hW.1.map_of_apply_eq_bot (fun d ↦ d.2.2) hν fun d h0 ↦ le_bot_iff.mp (h0 ▸ hle _)

/-- A grade-`1` face extends at the cap `⊥` to a lawful labelling, unchanged at grade `1`. -/
theorem exists_ext_bot (htbleg : tb.IsLegal) {W : Fin tb.card → Label.{u}} (hW : LawfulOne tb W) :
    ∃ W', tb.rows.IsLawful W' ∧ ∀ d, tb.toCellScheme.grade d ≤ 1 → W' d = W d := by
  have hle : (((univ : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_rfl, by omega⟩
  obtain ⟨q', hq', -, hq'w⟩ := (Rows.cappedLift_iff_forall_exists hle).mp
    (htbleg.isBountiful ⟨tb.univ_mem_faces, one_pos, by simp⟩
      ⟨tb.univ_mem_faces, two_pos, by simp⟩ hle) ⊥ (isSelfVisible_bot 2) (fun d ↦ W d)
    (fun _ ↦ ⊥) hW.1 (Rows.isLawfulBelow_const_bot _) (fun _ ↦ by simp)
  have hall (d : Fin tb.card) : d ∈ tb.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, tb.grade_le d⟩
  exact ⟨fun d ↦ q' ⟨d, hall d⟩, hq'.isLawful hall, fun d hd ↦ hq'w ⟨d, subset_univ _, hd⟩⟩

/-- **Donor raising with the gap at grade `1` on two points**, from the extension at the caps of
finite part `1` (`H2.GradeTwoExtAtOne`): every cell of the donor not labelled `⊤` is low, every
cell labelled `⊤` of grade at most `1`, off the root and not determined by the root is designated,
the designated cells have grade at most `1`, and every root cell is low or a root top in `A`.
Donor raising with the gap on the grade-`1` faces (`H2.donorRaisingGap_of_cappedLift` with
`H2.hasCappedLifts_lawfulOne`, `H2.lawfulOne_map`), then the extension to grade `2`
(`H2.exists_ext_two`). -/
theorem donorRaisingGap_one {t' : StageType.{u} α 2}
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) (hext : GradeTwoExtAtOne tb)
    {A : Set (Fin p.card)} {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops)
    (hTg : ∀ t ∈ Tops, tb.toCellScheme.grade t ≤ 1)
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A) :
    DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful A (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops := by
  set Lo1 := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1 with hLo1
  have he := StageType.comap_toScheme_of_restrictFace htbp
  have hrootg (x : Fin p.card) : tb.toCellScheme.grade (StageType.faceCell htbp x) ≤ 1 :=
    (StageType.grade_faceCell _ x).trans_le (p.grade_le x)
  have hroot1 : ∀ x, StageType.faceCell htbp x ∈ Lo1 ∨ x ∈ A := fun x ↦
    (hroot x).imp_left fun h ↦ mem_filter.mpr ⟨h, hrootg x⟩
  have hcls : ∀ d, d ∈ Lo1 ∨ d ∈ Tops ∨ (∃ x, StageType.faceCell htbp x = d) ∨
      IsRootDet (StageType.faceCell htbp) (LawfulOne tb) d := by
    intro d
    by_cases hdg : tb.toCellScheme.grade d ≤ 1
    swap
    · exact .inr (.inr (.inr fun W W' hW hW' _ ↦ (hW.2 d hdg).trans (hW'.2 d hdg).symm))
    by_cases hdt : tb.label d = ⊤
    swap
    · exact .inl (mem_filter.mpr ⟨hLo d hdt, hdg⟩)
    by_cases hdv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hdv
      exact .inr (.inr (.inl ⟨i, hi⟩))
    by_cases hdr : RootDet tb d
    · refine .inr (.inr (.inr fun W W' hW hW' hag ↦ ?_))
      obtain ⟨V, hV, hVW⟩ := exists_ext_bot htbleg hW
      obtain ⟨V', hV', hVW'⟩ := exists_ext_bot htbleg hW'
      have key := hdr V V' hV hV' fun y hy ↦ by
        obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq he hy
        exact (hVW _ (hrootg i)).trans ((hag i).trans (hVW' _ (hrootg i)).symm)
      exact (hVW d hdg).symm.trans (key.trans (hVW' d hdg))
    · exact .inr (.inl (hTops d hdt hdg hdv hdr))
  have hD1 : DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 1
      t'.rows.IsLawful (LawfulOne tb) A Lo1 Tops :=
    donorRaisingGap_of_cappedLift (hasCappedLifts_lawfulOne hp htbleg htbp)
      (fun hν hle _ hW ↦ lawfulOne_map hν hle hW) hroot1 hcls
  intro h c hh hc R f hR hf hagr hA hgap
  have hR1 : LawfulOne tb (spl tb R) := by
    refine ⟨?_, fun d hd ↦ spl_of_lt hd⟩
    convert hR.isLawfulBelow ((univ : Finset (Fin 2)), 1) using 1
    exact funext fun d ↦ spl_of_le d.2.2
  have hsup : Lo1.sup (spl tb R) = Lo1.sup R :=
    Finset.sup_congr rfl fun x hx ↦ spl_of_le (mem_filter.mp hx).2
  obtain ⟨W, hW, hWr, hWR, hWt⟩ := hD1 hh hc hR1 hf
    (fun x ↦ by rw [spl_of_le (hrootg x)]; exact hagr x) hA
    (fun t ht hlt ↦ by
      rw [hsup, spl_of_le (hTg t ht)] at hlt
      rw [spl_of_le (hTg t ht)]
      exact hgap t ht hlt)
  obtain ⟨W', hW', hW'W, hW'R⟩ := exists_ext_two htbleg hext hh hW.1 hR
    (fun d hd ↦ by rw [hWR d, spl_of_le hd])
  refine ⟨W', hW', fun x ↦ (hW'W _ (hrootg x)).trans (hWr x), hW'R, fun t ht hRt ↦ ?_⟩
  have hsupW : Lo1.sup W' = Lo1.sup W :=
    Finset.sup_congr rfl fun x hx ↦ hW'W x (mem_filter.mp hx).2
  rw [hW'W t (hTg t ht), hsupW]
  exact hWt t ht (by rwa [spl_of_le (hTg t ht)])

/-! ### The completion at top grade `1` from any admission of states -/

/-- **h2 at two points, top grade `1`, from the state admission at grade `1`**: the conclusion of
`H2.exists_completion_recProp_one` (on the research branch `research/port-low-padded`) from any
admission of states at grade `1` of the clause with the designated cells below the top read on their
cells of grade `1` (for instance from donor raising with the gap, `H2.donorRaisingGap_one`, and
owner lowering below the designated tops). -/
theorem exists_completion_recProp_one_of_admission {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    {n : ℕ} {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r)
    (hp : restrictFace Fin.castSuccEmb t' = some p)
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)}
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ 1)
    (hS : IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 (LawfulOne t')
      (LawfulOne tb) (SelfLowG o r 1 (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops)) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 1 Lo Tops := by
  set Lo1 := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1 with hLo1
  have hr1 : t'.toCellScheme.grade r ≤ 1 := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hloc : ReadsOne (Seed.ofCoatoms hleg htbleg hp htbp) (SelfLowG o r 1 Lo1 Tops) := by
    intro L L' R R' hL hR h t ht hlt
    have hRt : R' t = R t := (hR t (hTops t ht).2).symm
    have hsup : Lo1.sup R' = Lo1.sup R :=
      Finset.sup_congr rfl fun x hx ↦ (hR x (Finset.mem_filter.mp hx).2).symm
    have hfr : frontierAt o r 1 L' = frontierAt o r 1 L := by
      unfold frontierAt
      rw [← hL o hs.grade_owner.le, ← hL r hr1]
    have h' := h t ht ((congrArg (visibilityReplace 1 1) hsup.symm).trans_lt (hlt.trans_eq hRt))
    exact (le_of_eq hfr).trans (h'.trans_eq hRt.symm)
  have hst : SelfLowG o r 1 Lo1 Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  refine ⟨oneCompletion hS hloc hst, fun q hq hqo t ht hlt ↦ ?_⟩
  have hadm := adm_of_isLawful_layerTwo hS hloc (o := o) hs.grade_owner hq hqo
  refine hadm t ht (lt_of_le_of_lt ?_ hlt)
  exact monotone_visibilityReplace le_rfl (Finset.sup_mono (Finset.filter_subset _ _))

/-! ### Donor raising between the grade-`1` faces, with no hypothesis -/

/-- The root of a grade-`1` face is lawful. -/
theorem isLawful_root_of_lawfulOne {E : StageType.{u} α 2}
    (hE : restrictFace Fin.castSuccEmb E = some p) {f : Fin E.card → Label.{u}}
    (hf : LawfulOne E f) : p.rows.IsLawful fun i ↦ f (StageType.faceCell hE i) := by
  have he := StageType.comap_toScheme_of_restrictFace hE
  have hX : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin 1)), 1) ≤
      ((univ : Finset (Fin 2)), 1) := ⟨subset_univ _, le_rfl⟩
  have h1 : p.rows.IsLawfulBelow ((univ : Finset (Fin 1)), 1)
      (fun i ↦ f (StageType.faceCell hE i)) :=
    (Scheme.isLawfulBelow_faceCell_iff he _ f).mpr (by exact hf.1.mono hX)
  exact h1.isLawful fun d ↦ ⟨subset_univ _, p.grade_le d⟩

/-- **The capped lift between the grade-`1` faces**, from the root at grade `1`
(bountifulness of the donor). -/
theorem hasCappedLifts_lawfulOne_one {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    HasCappedLifts (StageType.faceCell hp) (StageType.faceCell htbp) 1 (LawfulOne t')
      (LawfulOne tb) := by
  intro h hh R f hR hf hagr
  -- `f` extended at the cap `⊥` to a lawful labelling of the context, with the same root
  obtain ⟨f', hf', hf'f⟩ := exists_ext_bot (tb := t') hleg hf
  have hr (x : Fin p.card) : f' (StageType.faceCell hp x) = f (StageType.faceCell hp x) :=
    hf'f _ ((StageType.grade_faceCell _ x).trans_le (p.grade_le x))
  obtain ⟨W, hW, hWr, hWR⟩ := hasCappedLifts_lawfulOne hp htbleg htbp hh hR hf'
    (fun x ↦ by rw [hr x]; exact hagr x)
  exact ⟨W, hW, fun x ↦ (hWr x).trans (hr x), hWR⟩

/-- **Donor raising with the gap between the grade-`1` faces at grade `1`**, with no hypothesis
beyond the designation: every cell of the donor not labelled `⊤` is low, every cell labelled `⊤`
of grade at most `1`, off the root and not determined by the root is designated, and every root
cell is low or a root top in `A` (`H2.donorRaisingGap_of_cappedLift` with
`H2.hasCappedLifts_lawfulOne_one` and `H2.lawfulOne_map`). -/
theorem donorRaisingGap_oneFace {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {A : Set (Fin p.card)} {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops)
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A) :
    DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 1 (LawfulOne t')
      (LawfulOne tb) A (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops := by
  set Lo1 := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1 with hLo1
  have he := StageType.comap_toScheme_of_restrictFace htbp
  have hrootg (x : Fin p.card) : tb.toCellScheme.grade (StageType.faceCell htbp x) ≤ 1 :=
    (StageType.grade_faceCell _ x).trans_le (p.grade_le x)
  have hcls : ∀ d, d ∈ Lo1 ∨ d ∈ Tops ∨ (∃ x, StageType.faceCell htbp x = d) ∨
      IsRootDet (StageType.faceCell htbp) (LawfulOne tb) d := by
    intro d
    by_cases hdg : tb.toCellScheme.grade d ≤ 1
    swap
    · exact .inr (.inr (.inr fun W W' hW hW' _ ↦ (hW.2 d hdg).trans (hW'.2 d hdg).symm))
    by_cases hdt : tb.label d = ⊤
    swap
    · exact .inl (mem_filter.mpr ⟨hLo d hdt, hdg⟩)
    by_cases hdv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hdv
      exact .inr (.inr (.inl ⟨i, hi⟩))
    by_cases hdr : RootDet tb d
    · refine .inr (.inr (.inr fun W W' hW hW' hag ↦ ?_))
      obtain ⟨V, hV, hVW⟩ := exists_ext_bot htbleg hW
      obtain ⟨V', hV', hVW'⟩ := exists_ext_bot htbleg hW'
      have key := hdr V V' hV hV' fun y hy ↦ by
        obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq he hy
        exact (hVW _ (hrootg i)).trans ((hag i).trans (hVW' _ (hrootg i)).symm)
      exact (hVW d hdg).symm.trans (key.trans (hVW' d hdg))
    · exact .inr (.inl (hTops d hdt hdg hdv hdr))
  exact @donorRaisingGap_of_cappedLift _ _ _ _ _ _ _ _ _ _ _
    (hasCappedLifts_lawfulOne_one hleg hp htbleg htbp)
    (fun hν hle _ hW ↦ lawfulOne_map hν hle hW)
    (fun x ↦ (hroot x).imp_left fun h ↦
      (mem_filter.mpr ⟨h, hrootg x⟩ : StageType.faceCell htbp x ∈ Lo1)) hcls

/-- **The order law and the frontier bound on the grade-`1` faces of a context of grade `1`**:
the owner is self-visible at `1`, and the frontier is at most every root top avoiding the lost
point (`StageType.IsSourceGapContextAt.frontier_le`, through a lawful labelling with the same cells
of grade `1`). -/
theorem frontier_le_lawfulOne {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r)
    (hp : restrictFace Fin.castSuccEmb t' = some p) {f : Fin t'.card → Label.{u}}
    (hf : LawfulOne t' f) :
    IsSelfVisible 1 (f o) ∧ ∀ a, p.label a = ⊤ →
      l ∉ t'.toCellScheme.scope (StageType.faceCell hp a) →
        frontierAt o r 1 f ≤ f (StageType.faceCell hp a) := by
  have ho : t'.toCellScheme.grade o ≤ 1 := hs.grade_owner.le
  have hr : t'.toCellScheme.grade r ≤ 1 := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  refine ⟨?_, fun a ha hla ↦ ?_⟩
  · have := (Rows.isLawfulBelow_iff_forall.mp hf.1).1 o ⟨subset_univ _, ho⟩
    rwa [hs.grade_owner] at this
  obtain ⟨f', hf', hf'f⟩ := exists_ext_bot (tb := t') hleg hf
  have hag : t'.toCellScheme.grade (StageType.faceCell hp a) ≤ 1 :=
    (StageType.grade_faceCell _ a).trans_le (p.grade_le a)
  have := hs.frontier_le hf' ((StageType.label_faceCell hp a).trans ha) hla
  unfold frontierAt
  rwa [hf'f o ho, hf'f r hr, hf'f _ hag] at this

/-- **The state admission between the grade-`1` faces at grade `1`**, from donor raising with the
gap (`H2.donorRaisingGap_oneFace`) and owner lowering between the grade-`1` faces (a
hypothesis). -/
theorem stateAdmission_oneFace {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops)
    {A : Set (Fin p.card)}
    (hA : ∀ a ∈ A, p.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope (StageType.faceCell hp a))
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A)
    (hOL : OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r 1 (LawfulOne t')
      (LawfulOne tb)) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 (LawfulOne t')
      (LawfulOne tb) (SelfLowG o r 1 (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops) :=
  selfLow_isStateAdmissionGap A
    (fun _ hf ↦ (frontier_le_lawfulOne hleg hs hp hf).1)
    (fun _ hf a ha ↦ (frontier_le_lawfulOne hleg hs hp hf).2 a (hA a ha).1 (hA a ha).2)
    (donorRaisingGap_oneFace hleg hp htbleg htbp hLo hTops hroot) hOL

end VaughtConjecture.H2

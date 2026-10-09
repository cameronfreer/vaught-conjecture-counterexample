/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelGrades

/-!
# The context lift of the next level of a re-rendered level

Roadmap, Layer 3 ((R3) and (R4), one level of the replicated carrier re-rendered per grade).

Over a good level `N` at the grade `j + 1` (`Seed.ALvl.Good`), with `j + 2 ≤ m + 1`, requests
calibrated on the class (`hQ`) with no relation between the threshold and `j + 2`, and the other
premises kept explicit until their proof is composed at the seed position (the labels pair correct,
`hpair`; the relative lift on the class, `hrel`; a legal donor, `hdL`; `0 < n`), the next level on
the catalogue at `j + 2` (`Seed.ALvl.next`, `Seed.lvCat`) lifts capped from the context coatom into
`(univ, j + 2)`, given the lift at the grade `j + 1` and a context cell at `(univ, j + 2)`
(`Seed.ALvl.Good.cappedLift_next`).

* **The admission premise at every grade** (`Seed.attachAdmits_truncate`,
  `Seed.exists_stateStep_admitted`): for an anchor admitted at `k`, the admission of its
  truncation at `k` is its own admission.  The donor cells have grade at most the arity
  `n + 1 ≤ threshold`, and the admission reads the context at the grades up to the threshold only
  (`GrowthRequests.admitsOnClass_congr_le_threshold`).  So the state step needs no relation
  between `k` and the threshold, and no catalogue structure of the anchor.
* **The state step for a catalogue anchor** (`Seed.exists_stateStep_level`): the anchor is lawful
  below the grade only; the step runs on its truncation, and above the grade the state is the
  anchor.
* **The serving rows.**  A cell at `(univ, j + 2)` is the cell of a state `R` of the catalogue; its
  row is the row labelling of `R` (`Seed.ALvl.Φ`): the section of the level at `R` and the agreement
  heights of `R` in the grid.
* **The short lift at a serving row** (`Seed.ALvl.Good.cappedLiftAtShort_next`): the state step
  gives a lawful admitted state `W`, literal on the context and agreeing with `R` capped at the cut;
  its orbit code `P` is a state of the catalogue agreeing with `R` capped at the cut
  (`Label.min_orbitCode_eq`, `R` canonical); the lift is the orbit decoder of `W` at the cut
  applied to the row labelling of `P`.  Its capped agreement with the row of `R`: at the cells of
  the level by readability (`Seed.ALvl.Good.readable`,
  `Label.min_orbitDecoder_eq_of_isReadableAt`: the key equality is derived from the capped
  agreement of the code, not assumed) and the capped agreement of the section
  (`Seed.ALvl.Good.capAgree`); at the new cells by the self-visibility of the agreement heights
  (`Label.min_orbitDecoder_eq`) and their capped agreement
  (`Label.min_agreementHeight_eq_of_isShort`).
* **The cap `⊥`** (`Seed.ALvl.Good.hasOwnerCappedLifts_next_bot`): the state step at the cut `⊥`
  from the bottom state, decoded at the least grid point.
* **The composition** (`Seed.ALvl.Good.cappedLift_next`):
  `CellScheme.Rows.hasOwnerCappedLifts_of_rows_short` and
  `CellScheme.Rows.cappedLift_of_ownerCappedLift`, with the rows consistent, short at `j + 2` and
  never the formal top.

No strict arity is used: the threshold may equal `n + 1`.  The copies of the replicated scheme at
the mixed faces are not part of these schemes.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-- A cell of the attachment below the context coatom is the cell of a context cell. -/
theorem exists_attachCtxCell_eq_of_mem {k : ℕ} {a : Fin (I.attachment g).card}
    (ha : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, k)) :
    ∃ x, I.attachCtxCell g x = a ∧ I.left.toCellScheme.grade x ≤ k := by
  have hvis : a ∈ (I.attachment g).visibleCells Fin.castSuccEmb := by
    rw [Scheme.mem_visibleCells]
    intro z hz
    have hz' : z ∈ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) := by
      rw [map_castSuccEmb_eq_ctxCoatom]
      exact ha.1 (mem_coe.mp hz)
    obtain ⟨y, -, rfl⟩ := mem_map.mp hz'
    exact ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq (I.restrictFace_left_attachmentType g) hvis
  exact ⟨x, rfl, (grade_attachCtxCell x).symm.trans_le ha.2⟩

/-- **The context section of a labelling of the attachment lawful below the context coatom** is a
lawful context section: the labelling at the context cells of grade at most `k`, `⊥` above. -/
theorem isLawful_ctxSectionOf {k : ℕ} {V : Fin (I.attachment g).card → Label.{u}}
    (hV : (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, k) fun t ↦ V t) :
    I.left.rows.IsLawful fun x ↦
      if (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ k then
        V (I.attachCtxCell g x) else ⊥ := by
  have h2 := Rows.isLawfulBelow_extendAbove (K := m + 2) hV
  have hX : Prod.map (Finset.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))) id
      ((univ : Finset (Fin (m + 1))), m + 2) = (ctxCoatom m, m + 2) := by
    simp only [Prod.map, id, map_castSuccEmb_eq_ctxCoatom]
  have h1 := ((I.attachment g).isLawfulBelow_comap_cellMap_iff Fin.castSuccEmb
    ((univ : Finset (Fin (m + 1))), m + 2)
    (fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then V a else ⊥)).mpr (hX ▸ h2)
  have h3 : ((I.attachment g).comap Fin.castSuccEmb).rows.IsLawful
      fun i ↦ (fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then V a else ⊥)
        ((I.attachment g).cellMap Fin.castSuccEmb i) :=
    Rows.isLawful_of_isLawfulBelow (fun i ↦ by
      refine ⟨subset_univ _, ?_⟩
      exact (attachment_mem_below_top ((I.attachment g).cellMap Fin.castSuccEmb i)).2) h1
  exact Scheme.isLawful_of_eq
    (comap_toScheme_of_restrictFace (I.restrictFace_left_attachmentType g)).symm h3

/-- **The admission on the class reads a section at the grades up to the threshold only**: the
class pattern is read at the cells below the cap, and the relation at the cap, the references and
the marker, all of grade at most the threshold (`ClassCalibrated`). -/
theorem _root_.VaughtConjecture.StageType.GrowthRequests.admitsOnClass_congr_le_threshold
    {k : ℕ} {t' : StageType.{u} α k} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    {e : Fin n ↪ Fin k} {hte : restrictFace e t' = some p₀}
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte)
    {s s' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hss : ∀ x, t'.toCellScheme.grade x ≤ Q.threshold → s' x = s x)
    (h : Q.AdmitsOnClass s v) : Q.AdmitsOnClass s' v := by
  intro hcls hcap j
  have hc : s' Q.cap = s Q.cap := hss _ le_rfl
  refine (h (fun x hx ↦ ?_) (hc ▸ hcap) j).congr hc.symm
    (fun hj ↦ (hss _ (hQ.ref j hj).1).symm) (hss _ hQ.marker.1).symm
  rw [← hss x hx.2]
  exact hcls x hx

/-- **The admission premise of the state step holds at every grade for an admitted anchor**: from
the threshold on, the admission of the truncation of `R₀` at `k` is the admission of `R₀` (read at
the threshold).  The donor cells have grade at most the arity `n + 1 ≤ threshold`, so both
truncations read the donor alike; on the context the admission reads the grades up to the
threshold only (`GrowthRequests.admitsOnClass_congr_le_threshold`). -/
theorem attachAdmits_truncate {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ}
    {R₀ : Fin (I.attachment g).card → Label.{u}} (hA : I.attachAdmits g hd Q k R₀) :
    Q.threshold ≤ k →
      Q.AdmitsOnClass
        (fun x ↦ if I.left.toCellScheme.grade x ≤ k then R₀ (I.attachCtxCell g x) else ⊥)
        fun y ↦ if d.toCellScheme.grade y ≤ k then R₀ (I.attachDonCell g hd y) else ⊥ := by
  intro hN
  have hdon (y : Fin d.card) : d.toCellScheme.grade y ≤ Q.threshold := by
    have h1 := d.isWellFormed.isWellFormed.grade_le_card y
    have h2 : #(d.toCellScheme.scope y) ≤ n + 1 :=
      (card_le_univ _).trans (by rw [Fintype.card_fin])
    exact h1.trans (h2.trans hQ.arity)
  have hgd (y : Fin d.card) :
      (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) = d.toCellScheme.grade y :=
    Scheme.grade_faceCell (I.comap_donor_attachment_scheme g hd) y
  have e2 : (fun y ↦ if d.toCellScheme.grade y ≤ k then R₀ (I.attachDonCell g hd y) else ⊥) =
      fun y ↦ I.attachHatAt g Q.threshold R₀ (I.attachDonCell g hd y) := by
    funext y
    unfold attachHatAt
    rw [hgd, ite_eq_left ((hdon y).trans hN), ite_eq_left (hdon y)]
  rw [e2]
  refine GrowthRequests.admitsOnClass_congr_le_threshold hQ (fun x hx ↦ ?_) (hA hN)
  change (if _ then _ else ⊥) = I.attachHatAt g Q.threshold R₀ (I.attachCtxCell g x)
  unfold attachHatAt
  rw [grade_attachCtxCell, ite_eq_left (hx.trans hN), ite_eq_left hx]

/-- **The state step for an admitted anchor at every grade**: a lawful anchor admitted at `k`
satisfies the admission premise of `Seed.exists_stateStep` (`Seed.attachAdmits_truncate`), with
no relation between `k` and the threshold. -/
theorem exists_stateStep_admitted {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {k : ℕ} (hk : 1 ≤ k) {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : (I.attachment g).rows.IsLawful R₀) (hR₀A : I.attachAdmits g hd Q k R₀)
    {h : Label.{u}} (hh : IsSelfVisible k h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell g x)) h) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep hte hdp hdL hn hd hQ hpair hrel hk hR₀ hh hw hwR
    fun hN _ ↦ attachAdmits_truncate (hte := hte) hQ hR₀A hN

/-- **The state step for an anchor of a catalogue** at every grade `k`: the anchor `R₀` is only
lawful below `(univ, k)`, with values self-visible at `1` and admitted at `k`.  The state step runs
on the truncation of `R₀` at `k` (lawful, `Scheme.isLawful_truncate`, admitted at `k` as `R₀` is,
`Seed.exists_stateStep_admitted`).  Above the grade `k` the state is set to `R₀`, so every value is
self-visible at `1`. -/
theorem exists_stateStep_level {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {k : ℕ} (hk : 1 ≤ k)
    {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) fun a ↦ R₀ a)
    (hR₀v : ∀ e, IsSelfVisible 1 (R₀ e)) (hR₀A : I.attachAdmits g hd Q k R₀)
    {h : Label.{u}} (hh : IsSelfVisible k h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell g x)) h) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧ (∀ a, min (W a) h = min (R₀ a) h) ∧
      ∀ e, IsSelfVisible 1 (W e) := by
  classical
  set T : Fin (I.attachment g).card → Label.{u} :=
    fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then R₀ a else ⊥ with hT
  have hTl : (I.attachment g).rows.IsLawful T := Scheme.isLawful_truncate hR₀
  have hTR (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a ≤ k) :
      T a = R₀ a := ite_eq_left ha
  have hwT (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ k) :
      min (w x) h = min (T (I.attachCtxCell g x)) h := by
    rw [hTR _ ((grade_attachCtxCell x).trans_le hx)]; exact hwR x hx
  obtain ⟨W, hWc, hWl, hWA, hWR⟩ : ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧ ∀ a, min (W a) h = min (T a) h := by
    refine exists_stateStep_admitted hte hdp hdL hn hd hQ hpair hrel hk hTl ?_ hh hw hwT
    by_cases hN : Q.threshold ≤ k
    · exact attachAdmits_congr hd (fun a ha ↦ hTR a (ha.trans hN)) hR₀A
    · exact fun hN' ↦ absurd hN' hN
  refine ⟨fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then W a else R₀ a,
    fun x hx ↦ ?_, ?_, ?_, fun a ↦ ?_, fun e ↦ ?_⟩
  · change (if _ then W _ else R₀ _) = _
    rw [ite_eq_left ((grade_attachCtxCell x).trans_le hx)]
    exact hWc x hx
  · refine (Rows.isLawfulBelow_congr (w := fun a ↦ W a)
      (w' := fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then W a else R₀ a)
      fun a ha ↦ ?_).mp hWl
    exact (ite_eq_left (ha.2 : (I.attachment g).toCellScheme.grade a ≤ k)).symm
  · by_cases hN : Q.threshold ≤ k
    · exact attachAdmits_congr hd (fun a ha ↦ ite_eq_left (ha.trans hN)) hWA
    · exact fun hN' ↦ absurd hN' hN
  · by_cases hak : (I.attachment g).toCellScheme.grade a ≤ k
    · change min (if _ then W a else R₀ a) h = _
      rw [ite_eq_left hak, hWR, hTR a hak]
    · change min (if _ then W a else R₀ a) h = _
      rw [ite_eq_right hak]
  · by_cases hek : (I.attachment g).toCellScheme.grade e ≤ k
    · change IsSelfVisible 1 (if _ then W e else R₀ e)
      rw [ite_eq_left hek]
      have ho := (Rows.isLawfulBelow_iff_forall.mp hWl).1 e ⟨subset_univ _, hek⟩
      exact ho.mono ((I.isWellFormed_attachment g).isWellFormed.grade_pos e)
    · change IsSelfVisible 1 (if _ then W e else R₀ e)
      rw [ite_eq_right hek]
      exact hR₀v e

namespace ALvl.Good

variable {j : ℕ} {H B : ℕ}
  {N : I.ALvl g H (j + 1)} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
  {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

variable (hN : N.Good B (lvAdm hd Q))
include hN

omit hN in
/-- A cell of the next scheme at `(univ, j + 2)` is a new cell. -/
theorem exists_natAdd_of_gradedIndex (C : Finset (Fin (I.attachment g).card → Label.{u}))
    {u : Fin (N.nS B C).card}
    (hu : (N.nS B C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), j + 2)) :
    ∃ i, u = Fin.natAdd _ i := by
  induction u using Fin.addCases with
  | left e =>
    exfalso
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hu
    exact N.not_le e hu.ge
  | right i => exact ⟨i, rfl⟩

/-- A cell of the next scheme below the context coatom is a cell of the attachment. -/
theorem exists_attEmb_of_mem_ctx (C : Finset (Fin (I.attachment g).card → Label.{u})) {k : ℕ}
    {z : Fin (N.nS B C).card} (hz : z ∈ (N.nS B C).toCellScheme.below (ctxCoatom m, k)) :
    ∃ a, z = Fin.castAdd _ (N.attEmb a) ∧
      a ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, k) := by
  induction z using Fin.addCases with
  | right i =>
    exfalso
    have h := hz.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact ne_univ_erase _ (univ_subset_iff.mp h)
  | left e =>
    have hz' := hz
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hz'
    have hsc : N.S.toCellScheme.scope e ⊆ ctxCoatom m := hz'.1
    obtain ⟨a, rfl⟩ := hN.mem_range e fun h ↦ ne_univ_erase _ (univ_subset_iff.mp (h ▸ hsc))
    refine ⟨a, rfl, ?_⟩
    rw [CellScheme.mem_below, ← hN.gradedIndex_attEmb]
    exact hz'

/-- Lawfulness below the context coatom in the next scheme is lawfulness on the attachment. -/
theorem isLawfulBelow_ctx_iff (C : Finset (Fin (I.attachment g).card → Label.{u})) {k : ℕ}
    {w : Fin (N.nS B C).card → Label.{u}} :
    (N.nS B C).rows.IsLawfulBelow (ctxCoatom m, k) (fun z ↦ w z) ↔
      (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, k)
        (fun a ↦ w (Fin.castAdd _ (N.attEmb a))) := by
  rw [Scheme.isLawfulBelow_appendFullCells_iff fun h ↦ ne_univ_erase _ (univ_subset_iff.mp h.1)]
  exact hN.isLawfulBelow_old_iff (X := (ctxCoatom m, k)) (ne_univ_erase _)
    (w := fun e ↦ w (Fin.castAdd _ e))

/-- **The short lift at a serving row of the next level** at the top grade `j + 2` (see the module
docstring). -/
theorem cappedLiftAtShort_next
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hB : 2 * (I.attachment g).card ≤ B) {u : Fin (N.nS B (I.lvCat g B hd Q (j + 2))).card}
    (hu : (N.nS B (I.lvCat g B hd Q (j + 2))).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), j + 2)) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLiftAtShort (ctxCoatom_le (j + 2))
      ((N.nS B (I.lvCat g B hd Q (j + 2))).rows.rowBelow u hu) := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  intro h hh hs hb f hf _ hfS
  obtain ⟨i, rfl⟩ := exists_natAdd_of_gradedIndex C hu
  set R := (C.equivFin.symm i).1 with hRdef
  obtain ⟨hRB, hRl, hRv, hRc, hRA⟩ := mem_lvCat.mp (C.equivFin.symm i).2
  have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
  have hS (e : (N.nS B C).toCellScheme.below ((univ : Finset (Fin (m + 2))), j + 2)) :
      (N.nS B C).rows.rowBelow (Fin.natAdd _ i) hu e = N.Φ B C R e.1 :=
    Scheme.appendFullCells_row_natAdd i _
  -- the prescription, on the attachment and on the context
  set fT := Rows.extendBot (ctxCoatom m, j + 2) f with hfT
  have hV : (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, j + 2)
      fun a ↦ fT (Fin.castAdd _ (N.attEmb a)) :=
    (hN.isLawfulBelow_ctx_iff C).mp (Rows.isLawfulBelow_extendBot.mpr hf)
  set w : Fin I.left.card → Label.{u} := fun x ↦
    if (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ j + 2 then
      fT (Fin.castAdd _ (N.attEmb (I.attachCtxCell g x))) else ⊥ with hw
  have hwl : I.left.rows.IsLawful w :=
    isLawful_ctxSectionOf (V := fun a ↦ fT (Fin.castAdd _ (N.attEmb a))) hV
  have hmemX (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ j + 2) :
      Fin.castAdd C.card (N.attEmb (I.attachCtxCell g x)) ∈
        (N.nS B C).toCellScheme.below (ctxCoatom m, j + 2) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      hN.gradedIndex_attEmb]
    exact ⟨scope_attachCtxCell_subset x, (grade_attachCtxCell x).trans_le hx⟩
  have hwx (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ j + 2) :
      w x = f ⟨_, hmemX x hx⟩ := by
    rw [hw]
    dsimp only
    rw [ite_eq_left ((grade_attachCtxCell x).trans_le hx)]
    exact Rows.extendBot_of_mem f (hmemX x hx)
  have hwR (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ j + 2) :
      min (w x) h = min (R (I.attachCtxCell g x)) h := by
    rw [hwx x hx, hfS, hS]
    change min (N.Φ B C R (Fin.castAdd _ (N.attEmb (I.attachCtxCell g x)))) h = _
    rw [ALvl.Φ_castAdd, hN.literal R hR1]
  -- the state step at the grade `j + 2`
  obtain ⟨W, hWctx, hWl, hWA, hWR, hWv⟩ := exists_stateStep_level hte hdp hdL hn hd hQ hpair
    hrel (by omega) hRl hRv hRA hh (hwl.isLawfulBelow _) hwR
  set P := orbitCode (j + 2) W with hPdef
  have hPC : P ∈ C := mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _,
    hWl.orbitCode fun e ↦ e.2.2, fun e ↦ isSelfVisible_one_orbitCode (by omega) (hWv e),
    orbitCode_orbitCode, attachAdmits_orbitCode hQ hWA⟩
  obtain ⟨hPB, hPl, -, hPc, -⟩ := mem_lvCat.mp hPC
  have hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ P e) := hPl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hPR : ∀ a, min (P a) h = min (R a) h := min_orbitCode_eq hh hs hRc hWR
  have hPW : ∀ a, min (orbitCode (j + 2) W a) h = min (W a) h :=
    fun a ↦ (hPR a).trans (hWR a).symm
  refine ⟨fun z ↦ orbitDecoder (j + 2) W h (N.Φ B C P z.1),
    (hN.isLawfulBelow_Φ hPC).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb.ne') (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb.ne'),
    fun e ↦ ?_, fun z ↦ ?_⟩
  · -- the prescription on the context coatom
    obtain ⟨a, he, ha⟩ := hN.exists_attEmb_of_mem_ctx C e.2
    obtain ⟨x, rfl, hx⟩ := exists_attachCtxCell_eq_of_mem ha
    have hfe : f e = w x := by
      rw [hwx x hx]; congr 1; exact Subtype.ext he
    change orbitDecoder (j + 2) W h (N.Φ B C P e.1) = f e
    rw [hfe, he, ALvl.Φ_castAdd, hN.literal P hP1, orbitDecoder_orbitCode hPW]
    exact hWctx x hx
  · -- the capped agreement with the row of `R`
    rw [hS z]
    obtain ⟨z, -⟩ := z
    dsimp only
    induction z using Fin.addCases with
    | left e =>
      rw [ALvl.Φ_castAdd, ALvl.Φ_castAdd,
        min_orbitDecoder_eq_of_isReadableAt hh hPW (hN.readable P hPc hPB hP1 e)]
      exact hN.capAgree P R hP1 hR1 hPB h hh hs hPR e
    | right i' =>
      rw [ALvl.Φ_natAdd, ALvl.Φ_natAdd, min_orbitDecoder_eq
        (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs (fun e ↦ ⟨hPB e, hRB e⟩) hPR _

/-- **The owner-capped lift at the cap `⊥` of the next level** at the top grade `j + 2`: the
prescription capped at its owner label, its context section, the state step at the cut `⊥` from
the bottom state (`Seed.exists_stateStep_level`), and the orbit decoder at the least grid point
applied to the row labelling of the code (a state of the catalogue). -/
theorem hasOwnerCappedLifts_next_bot (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hdL : d.IsLegal) (hn : 0 < n) (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hB : 2 * (I.attachment g).card ≤ B) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.HasOwnerCappedLifts
      (erase_subset (Fin.last (m + 1)) univ) (j + 1) ⊥ := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  intro p q hp _ _ o ho _ _
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
  have hM : IsSelfVisible (j + 1 + 1) (p o) := hp.isSelfVisible_of_gradedIndex_eq ho
  have hp' := hp.min_const_of_isSelfVisible hM
  set pT := Rows.extendBot (univ.erase (Fin.last (m + 1)), j + 1 + 1)
    (fun e ↦ min (p e) (p o)) with hpT
  have hV : (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, j + 2)
      fun a ↦ pT (Fin.castAdd _ (N.attEmb a)) :=
    (hN.isLawfulBelow_ctx_iff C).mp (Rows.isLawfulBelow_extendBot.mpr hp')
  set w : Fin I.left.card → Label.{u} := fun x ↦
    if (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ j + 2 then
      pT (Fin.castAdd _ (N.attEmb (I.attachCtxCell g x))) else ⊥ with hw
  have hwl : I.left.rows.IsLawful w :=
    isLawful_ctxSectionOf (V := fun a ↦ pT (Fin.castAdd _ (N.attEmb a))) hV
  obtain ⟨W, hWctx, hWl, hWA, -, hWv⟩ := exists_stateStep_level hte hdp hdL hn hd hQ hpair hrel
    (k := j + 2) (by omega) (R₀ := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
    (fun _ ↦ isSelfVisible_bot 1)
    (I.attachAdmits_bot g hd Q _) (isSelfVisible_bot _) (hwl.isLawfulBelow _)
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  set P := orbitCode (j + 2) W with hPdef
  have hPC : P ∈ C := mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _,
    hWl.orbitCode fun e ↦ e.2.2, fun e ↦ isSelfVisible_one_orbitCode (by omega) (hWv e),
    orbitCode_orbitCode, attachAdmits_orbitCode hQ hWA⟩
  obtain ⟨-, hPl, -, -, -⟩ := mem_lvCat.mp hPC
  have hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ P e) := hPl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hPW (a : Fin (I.attachment g).card) :
      min (orbitCode (j + 2) W a) (gridPoint (j + 2) 0) = min (W a) (gridPoint (j + 2) 0) :=
    min_orbitCode_gridPoint_zero a
  refine ⟨fun z ↦ orbitDecoder (j + 2) W (gridPoint (j + 2) 0) (N.Φ B C P z.1),
    (hN.isLawfulBelow_Φ hPC).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun e ↦ ?_,
    fun _ ↦ by rw [min_bot_right, min_bot_right]⟩
  obtain ⟨a, he, ha⟩ := hN.exists_attEmb_of_mem_ctx C e.2
  obtain ⟨x, rfl, hx⟩ := exists_attachCtxCell_eq_of_mem ha
  change orbitDecoder (j + 2) W (gridPoint (j + 2) 0) (N.Φ B C P e.1) = min (p e) (p o)
  rw [he, ALvl.Φ_castAdd, hN.literal P hP1, orbitDecoder_orbitCode hPW, hWctx x hx, hw]
  dsimp only
  rw [ite_eq_left ((grade_attachCtxCell x).trans_le hx), ← he]
  exact Rows.extendBot_of_mem _ e.2

/-- **The context lift of the next level at the grade `j + 2 ≤ m + 1`**, for requests calibrated
on the class at any threshold (`hQ`; no relation between the threshold and `j + 2`), with the
labels pair correct (`hpair`), the relative lift on the class (`hrel`), a legal donor (`hdL`),
`0 < n`, and a context cell at `(univ, j + 2)`; these premises stay explicit until their proof is
composed at the seed position.  The lift at the grade `j + 1` and the owner-capped
lifts at every cap self-visible at `j + 2` (at `⊥`,
`Seed.ALvl.Good.hasOwnerCappedLifts_next_bot`; at a positive cap from the serving rows,
`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`, the rows consistent, short at `j + 2` and
never the formal top, and the short lift
`Seed.ALvl.Good.cappedLiftAtShort_next`) compose by
`CellScheme.Rows.cappedLift_of_ownerCappedLift`. -/
theorem cappedLift_next (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hdL : d.IsLegal) (hn : 0 < n) (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hkm : j + 2 ≤ m + 1)
    (hB : 2 * (I.attachment g).card ≤ B)
    (hX : ∃ x : Fin I.left.card,
      I.left.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 1))), j + 2))
    (hlift : (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1))
      ⟨erase_subset _ _, le_rfl⟩) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 2)) (Y := ((univ : Finset (Fin (m + 2))), j + 2))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  have hNext := hN.next hQ (by omega) hB
  have hbot : (fun _ ↦ ⊥ : Fin (I.attachment g).card → Label.{u}) ∈ C :=
    mem_lvCat.mpr ⟨fun _ ↦ mem_insert_self _ _, Rows.isLawfulBelow_const_bot _,
      fun _ ↦ isSelfVisible_bot 1, funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl,
      I.attachAdmits_bot g hd Q _⟩
  have hY : ∃ t : Fin (N.nS B C).card, (N.nS B C).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin (m + 2))), j + 1 + 1) :=
    ⟨Fin.natAdd _ (C.equivFin ⟨_, hbot⟩), Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩
  refine Rows.cappedLift_of_ownerCappedLift (j := j + 1) (erase_subset _ _) ?_ hlift
    fun c hc ↦ ?_
  · obtain ⟨x, hx⟩ := hX
    refine ⟨Fin.castAdd _ (N.attEmb (I.attachCtxCell g x)), ?_⟩
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hN.gradedIndex_attEmb]
    refine Prod.ext ?_ ((grade_attachCtxCell x).trans (congrArg Prod.snd hx))
    change (I.attachment g).toCellScheme.scope (I.attachCtxCell g x) = _
    have hsx : I.left.toCellScheme.scope x = univ := congrArg Prod.fst hx
    rw [attachCtxCell, Scheme.scope_faceCell, hsx]
    exact map_castSuccEmb_eq_ctxCoatom
  · by_cases hc0 : c = ⊥
    · subst hc0
      exact hN.hasOwnerCappedLifts_next_bot hdp hdL hn hQ hpair hrel hB
    refine Rows.hasOwnerCappedLifts_of_rows_short (erase_subset _ _) (bot_lt_iff_ne_bot.mpr hc0)
      hc hY fun u hu ↦ ⟨hNext.consistent u, fun e ↦ ?_, fun e ↦ ?_,
        hN.cappedLiftAtShort_next hdp hdL hn hQ hpair hrel hB hu⟩
    all_goals
      obtain ⟨i, rfl⟩ := exists_natAdd_of_gradedIndex C hu
      obtain ⟨hRB, hRl, -, -, -⟩ := mem_lvCat.mp (C.equivFin.symm i).2
      have hmem := hN.Φ_mem_codeGrid C hRB
        (hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) e.1
      rw [show (N.nS B C).rows.rowBelow (Fin.natAdd _ i) hu e = N.Φ B C (C.equivFin.symm i).1 e.1
        from Scheme.appendFullCells_row_natAdd i _]
    · exact isShort_of_mem_codeGrid hmem
    · exact ne_top_of_le_ne_top (gridPoint_ne_top _ _) (le_gridPoint_of_mem_codeGrid hmem)

end ALvl.Good

end Seed

end VaughtConjecture

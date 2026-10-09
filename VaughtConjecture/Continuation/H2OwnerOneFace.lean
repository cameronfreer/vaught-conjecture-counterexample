/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OwnerOne
import VaughtConjecture.Continuation.H2OneRaise

/-!
# Owner lowering at grade `1` between the grade-`1` faces (work file)

WORK FILE (branch `research/work-owner-one`).  Every declaration here is proved.

The engine of top grade `1` runs on the **grade-`1` faces** (`H2.LawfulOne`: lawful below
`(univ, 1)` and `⊥` at the cells of grade `2`).  Between them, owner lowering below the designated
tops holds at grade `1` (`H2.ownerLoweringBelow_oneFace`) at a legal source-gap context of grade
`1` on two points **whose owner is the only cell of its graded index** `(univ, 1)` (a named
condition), for a legal donor with the same root face whose root cells are designated low or are
root tops avoiding the lost point.

**The construction.**  Take the capped lift from the root of the donor face at the cap `h`
(bountifulness), and cap it at `c`, the least designated top concerned, at the cells read by the
owner at most the **threshold** `visibilityReplace 1 1 (rowAt o r)` (`H2.capBelow`).  The lost top
is among them, so the frontier is at most `c`.  The root is kept: the root tops avoiding the lost
point are read strictly above the threshold (the strict source gaps), and the low root cells are
below `c`.  The capped labelling is a grade-`1` face (`H2.lawfulOne_capBelow`):
* at a capped cell, locality is that of the lift capped at `c`;
* at a cell `s` not capped, the row of the owner is lawful (consistency), so its values below `s`,
  capped at its value at `s`, are a transformation `τ` of the row of `s`; the capped cells below
  `s` are those whose argument has `τ`-image at most the threshold, a set closed downward and
  invariant under replacement at `1`, and capping the shifter of `s` there gives a witness
  (`H2.isWitness_capBelow`);
* availability into `(univ, 1)` is served by the owner, which is read above the threshold and is
  the only cell there (the named condition is used only here); availability within a graded index
  is served by the cell itself.

**Composition.**  With donor raising with the gap (`H2.donorRaisingGap_oneFace`) and the frontier
bound (`H2.frontier_le_lawfulOne`), the clause is an admission of states between the grade-`1`
faces (`H2.stateAdmission_oneFace_of_owner`, through `H2.selfLow_isStateAdmissionGap_of_below`),
and the conclusion of the case of top grade `1` follows
(`H2.exists_completion_recProp_one_of_owner`, through
`H2.exists_completion_recProp_one_of_admission`).  Both contexts of
`VaughtConjecture.Continuation.H2OwnerOne` have their owner alone at its graded index, so the
clause is an admission of states between their grade-`1` faces
(`OwnerGradeOne.isStateAdmission_oneFace`, `OwnerGradeOneTop.isStateAdmission_oneFace`): their
refutations concern the full labellings.

**Open.**  Owner lowering below the designated tops between the grade-`1` faces when another cell
shares the graded index of the owner: the capped labelling may then lose a cell of `(univ, 1)`
that served a root top or a cell of `({1}, 1)` read above the threshold.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission CellScheme

/-! ### Capping the targets of a row below a threshold of another reading -/

/-- Every label is self-visible at `0`. -/
theorem isSelfVisible_zero_any (x : Label.{u}) : IsSelfVisible 0 x := by
  induction x using recBotCoeTop with
  | bot => exact isSelfVisible_bot 0
  | coe o => exact isSelfVisible_coe.mpr (by simp)
  | top => exact isSelfVisible_top 0

/-- **Capping a shifter below a threshold of another reading.**  Let `(g, σ)` be a witness, let
`(gτ, τ)` be a witness, and let `θ` be self-visible at `1` and below `gτ 1`.  Capping `σ` at a
label `c > ⊥` self-visible at `1` at the arguments `x` with `τ x ≤ θ` gives a witness with the
suppressor truncated above `1`: the set `τ x ≤ θ` is closed downward and invariant under
replacement at `1`. -/
theorem isWitness_capBelow {g gτ : ℕ → Label.{u}} {σ τ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) (hτ : IsWitness gτ τ) {θ c : Label.{u}} (hθ : IsSelfVisible 1 θ)
    (hθg : θ < gτ 1) (hc : IsSelfVisible 1 c) (hc0 : ⊥ < c) :
    IsWitness (fun n ↦ if n ≤ 1 then g n else ⊥)
      (fun x ↦ if τ x ≤ θ then min (σ x) c else σ x) := by
  have hw' := hw.truncate 1
  -- the set `τ x ≤ θ` is invariant under replacement at `1`
  have hinv (x : Label.{u}) (i : ℕ) (hi : i ≤ 1) :
      τ (visibilityReplace 1 i x) ≤ θ ↔ τ x ≤ θ := by
    constructor
    · intro h
      exact (hτ.monotone (le_visibilityReplace (by omega) x)).trans h
    · intro h
      rw [hτ.visibilityReplace_comm x 1 (h.trans hθg.le) i hi]
      calc visibilityReplace 1 i (τ x) ≤ visibilityReplace 1 i θ :=
            monotone_visibilityReplace hi h
        _ = θ := hθ.visibilityReplace_eq i
  refine ⟨hw'.antitone, hw'.isSelfVisible, ?_, ?_, ?_⟩
  · simp only [hw.map_bot, hτ.map_bot, bot_le, ite_true, min_eq_left]
  · intro x y hxy
    simp only
    split_ifs with h1 h2 h2
    · exact min_le_min_right c (hw.monotone hxy)
    · exact (min_le_left _ _).trans (hw.monotone hxy)
    · exact absurd ((hτ.monotone hxy).trans h2) h1
    · exact hw.monotone hxy
  · intro x k hx i hi
    rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
    · rw [(isSelfVisible_zero_any x).visibilityReplace_eq,
        (isSelfVisible_zero_any _).visibilityReplace_eq]
    · simp only [hinv x i hi]
      split_ifs with hP
      · have hx' : min (σ x) c ≤ g 1 := by simpa [hP] using hx
        rw [visibilityReplace_min hi, hc.visibilityReplace_eq]
        by_cases hσ : σ x ≤ g 1
        · rw [hw.visibilityReplace_comm x 1 hσ i hi]
        · have hcg : c ≤ g 1 := by
            rcases le_total (σ x) c with h | h
            · exact absurd ((min_eq_left h) ▸ hx') hσ
            · exact (min_eq_right h) ▸ hx'
          have hlt : c < σ x := (hcg.trans_lt (not_le.mp hσ))
          rw [min_eq_right ((hlt.le).trans (hw.monotone (le_visibilityReplace (by omega) x))),
            min_eq_right (hlt.le.trans (le_visibilityReplace (by omega) _))]
      · have hx' : σ x ≤ g 1 := by simpa [hP] using hx
        exact hw.visibilityReplace_comm x 1 hx' i hi
    · have hx' : (if τ x ≤ θ then min (σ x) c else σ x) = ⊥ := by
        simpa only [show ¬ k ≤ 1 by omega, ite_false, le_bot_iff] using hx
      have hσ0 : σ x = ⊥ := by
        split_ifs at hx' with hP
        · rcases le_total (σ x) c with h | h
          · exact (min_eq_left h) ▸ hx'
          · exact absurd ((min_eq_right h) ▸ hx') hc0.ne'
        · exact hx'
      have hcomm := hw'.visibilityReplace_comm x k (by
        simp only [show ¬ k ≤ 1 by omega, ite_false, hσ0, le_refl]) i hi
      rw [hσ0, visibilityReplace_bot] at hcomm
      have hle : (if τ (visibilityReplace k i x) ≤ θ then min (σ (visibilityReplace k i x)) c
          else σ (visibilityReplace k i x)) ≤ σ (visibilityReplace k i x) := by
        split_ifs
        · exact min_le_left _ _
        · exact le_rfl
      rw [hx', visibilityReplace_bot]
      exact le_bot_iff.mp (hcomm ▸ hle)

/-! ### Capping the cells read by the owner at most the lost top -/

section Cap

variable {α : Ordinal.{u}} {t' : StageType.{u} α 2} {n : ℕ} {g₀ : Fin n ↪ Fin 2} {l : Fin 2}
  {o r : Fin t'.card}

/-- The **threshold** of a context at the owner: the replaced reading of the lost top. -/
noncomputable def threshold (t' : StageType.{u} α 2) (o r : Fin t'.card) : Label.{u} :=
  visibilityReplace 1 1 (t'.rowAt o r)

/-- **The labelling capped below the threshold**: capped at `c` at the cells read by the owner at
most the threshold. -/
noncomputable def capBelow (t' : StageType.{u} α 2) (o r : Fin t'.card)
    (W : Fin t'.card → Label.{u}) (c : Label.{u}) (d : Fin t'.card) : Label.{u} :=
  if t'.rowAt o d ≤ threshold t' o r then min (W d) c else W d

theorem capBelow_le (W : Fin t'.card → Label.{u}) (c : Label.{u}) (d : Fin t'.card) :
    capBelow t' o r W c d ≤ W d := by
  unfold capBelow
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem capBelow_of_le {W : Fin t'.card → Label.{u}} {c : Label.{u}} {d : Fin t'.card}
    (hd : t'.rowAt o d ≤ threshold t' o r) : capBelow t' o r W c d = min (W d) c := by
  simp only [capBelow, hd, ↓reduceIte]

theorem capBelow_of_not_le {W : Fin t'.card → Label.{u}} {c : Label.{u}} {d : Fin t'.card}
    (hd : ¬ t'.rowAt o d ≤ threshold t' o r) : capBelow t' o r W c d = W d := by
  simp only [capBelow, hd, ↓reduceIte]

theorem gradedIndex_owner (hs : t'.IsSourceGapContextAt 1 g₀ l o r) :
    t'.toCellScheme.gradedIndex o = ((univ : Finset (Fin 2)), 1) :=
  Prod.ext hs.scope_owner hs.grade_owner

theorem mem_below_owner_iff (hs : t'.IsSourceGapContextAt 1 g₀ l o r) (d : Fin t'.card) :
    d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) ↔ t'.toCellScheme.grade d ≤ 1 := by
  rw [gradedIndex_owner hs]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨subset_univ _, h⟩⟩

/-- **Capping below the threshold keeps a grade-`1` face**, at a context of grade `1` whose owner
is the only cell of its graded index, for a cap `c > ⊥` self-visible at `1`.  At a cell outside
the capped set the targets are capped exactly at the arguments read below the threshold by the
row of the owner (`H2.isWitness_capBelow`), a set closed downward in the row of the cell since the
row of the owner is lawful (consistency); availability into the owner is served by the owner,
which is read above the threshold. -/
theorem lawfulOne_capBelow (hleg : t'.IsLegal) (hs : t'.IsSourceGapContextAt 1 g₀ l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {W : Fin t'.card → Label.{u}} (hW : LawfulOne t' W) {c : Label.{u}} (hc : IsSelfVisible 1 c)
    (hc0 : ⊥ < c) : LawfulOne t' (capBelow t' o r W c) := by
  classical
  set X := t'.toCellScheme.gradedIndex o with hX
  set θ := threshold t' o r
  have hgi := gradedIndex_owner hs
  have hθ : IsSelfVisible 1 θ := visibilityReplace_self_visibilityReplace le_rfl _
  have hθo : θ < t'.rowAt o o := hs.gap_owner
  have hgrade1 (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ 1) :
      t'.toCellScheme.grade d = 1 :=
    le_antisymm hd (t'.isWellFormed.isWellFormed.grade_pos d)
  -- the grade-`1` face below the graded index of the owner
  have hWX : t'.rows.IsLawfulBelow X (fun d ↦ W d) := by rw [hX, hgi]; exact hW.1
  obtain ⟨hWo, hWl, hWa⟩ := Rows.isLawfulBelow_iff_forall.mp hWX
  -- the row of the owner is lawful below its graded index
  have hRX : t'.rows.IsLawfulBelow X (fun d ↦ t'.rowAt o d) := by
    convert hleg.isConsistent o using 1
    funext d
    exact Scheme.rowAt_of_mem d.2
  obtain ⟨-, hRl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hRX
  have hmem (d : Fin t'.card) : d ∈ t'.toCellScheme.below X ↔ t'.toCellScheme.grade d ≤ 1 :=
    mem_below_owner_iff hs d
  refine ⟨?_, fun d hd ↦ ?_⟩
  swap
  · exact le_bot_iff.mp ((capBelow_le W c d).trans (hW.2 d hd).le)
  have key : t'.rows.IsLawfulBelow X (fun d ↦ capBelow t' o r W c d) := by
    refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs' ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · -- order
      unfold capBelow
      split_ifs
      · exact (hWo d hd).min (hc.mono ((hmem d).mp hd))
      · exact hWo d hd
    · -- locality
      have hs1 : t'.toCellScheme.grade s = 1 := hgrade1 s ((hmem s).mp hs')
      have hgle (d : t'.toCellScheme.below (t'.toCellScheme.gradedIndex s)) :
          t'.toCellScheme.grade d.1 ≤ 1 := hs1 ▸ d.2.2
      by_cases hZs : t'.rowAt o s ≤ θ
      · convert (hWl s hs').min_const hgle hc using 2 with d
        rw [capBelow_of_le hZs]
        by_cases hZd : t'.rowAt o d ≤ θ
        · rw [capBelow_of_le hZd, min_min_min_comm, min_self]
        · rw [capBelow_of_not_le hZd, min_assoc]
      · obtain ⟨g, σ, hw, heq⟩ := hWl s hs'
        obtain ⟨gτ, τ, hτ, heqτ⟩ := hRl s hs'
        have hθs : θ < t'.rowAt o s := not_le.mp hZs
        have hgτ : θ < gτ 1 := by
          have e : min (t'.rowAt o s) (t'.rowAt o s) = min (τ (t'.rows.row s
              ⟨s, t'.toCellScheme.mem_below_gradedIndex s⟩)) (gτ (t'.toCellScheme.grade s)) :=
            heqτ ⟨s, t'.toCellScheme.mem_below_gradedIndex s⟩
          rw [min_self, hs1] at e
          exact hθs.trans_le (e ▸ min_le_right _ _)
        refine ⟨_, _, isWitness_capBelow hw hτ hθ hgτ hc hc0, fun d ↦ ?_⟩
        have hd1 : t'.toCellScheme.grade d.1 = 1 := hgrade1 d.1 (hgle d)
        have e : min (W d) (W s) = min (σ (t'.rows.row s d)) (g 1) := by
          have := heq d
          rw [← hd1]
          exact this
        have eτ : min (t'.rowAt o d) (t'.rowAt o s) = min (τ (t'.rows.row s d)) (gτ 1) := by
          have := heqτ d
          rw [← hd1]
          exact this
        change min (capBelow t' o r W c d) (capBelow t' o r W c s) =
          min (if τ (t'.rows.row s d) ≤ θ then min (σ (t'.rows.row s d)) c
            else σ (t'.rows.row s d)) (if t'.toCellScheme.grade d.1 ≤ 1 then g _ else ⊥)
        simp only [hgle d, ↓reduceIte]
        rw [hd1, capBelow_of_not_le hZs]
        by_cases hP : τ (t'.rows.row s d) ≤ θ
        · have hZd : t'.rowAt o d ≤ θ := by
            have h1 : min (t'.rowAt o d) (t'.rowAt o s) ≤ θ := by
              rw [eτ, min_eq_left (hP.trans hgτ.le)]
              exact hP
            rcases le_total (t'.rowAt o d) (t'.rowAt o s) with h | h
            · rwa [min_eq_left h] at h1
            · rw [min_eq_right h] at h1
              exact absurd h1 (not_le.mpr hθs)
          simp only [hP, ↓reduceIte]
          rw [capBelow_of_le hZd, min_right_comm, e, min_right_comm]
        · have hZd : ¬ t'.rowAt o d ≤ θ := by
            intro hZd
            have h1 : min (t'.rowAt o d) (t'.rowAt o s) ≤ θ := (min_le_left _ _).trans hZd
            rw [eτ] at h1
            rcases le_total (τ (t'.rows.row s d)) (gτ 1) with h | h
            · exact hP ((min_eq_left h) ▸ h1)
            · exact absurd ((min_eq_right h) ▸ h1) (not_le.mpr hgτ)
          simp only [hP, ↓reduceIte]
          rw [capBelow_of_not_le hZd, e]
    · -- availability
      have ht1 : t'.toCellScheme.grade t = 1 := hgrade1 t ((hmem t).mp ht)
      by_cases hsu : t'.toCellScheme.scope t = univ
      · have hto : t'.toCellScheme.gradedIndex t = t'.toCellScheme.gradedIndex o :=
          (Prod.ext hsu ht1).trans hgi.symm
        obtain ⟨u, hu, hle⟩ := hWa s t ht hst hg
        have huo : u = o := honly u (hu.trans hto)
        subst huo
        refine ⟨u, hu, (capBelow_le W c s).trans (hle.trans ?_)⟩
        rw [capBelow_of_not_le (not_le.mpr hθo)]
      · refine ⟨s, ?_, le_rfl⟩
        have hne : (t'.toCellScheme.scope s).Nonempty := by
          have h1 := t'.isWellFormed.isWellFormed.grade_pos s
          have h2 := t'.isWellFormed.isWellFormed.grade_le_card s
          exact Finset.card_pos.mp (h1.trans_le h2)
        have k : ∀ A B : Finset (Fin 2), A ⊆ B → A.Nonempty → B ≠ univ → A = B := by decide
        exact Prod.ext (k _ _ hst hne hsu) hg
  rw [hX, hgi] at key
  exact key

end Cap

/-! ### Owner lowering below the designated tops between the grade-`1` faces -/

variable {α : Ordinal.{u}}

/-- **Owner lowering below the designated tops between the grade-`1` faces at grade `1`**, at a
legal source-gap context of grade `1` on two points whose owner is the only cell of its graded
index, for a legal donor with the same root face, every root cell of the donor designated low or a
root top avoiding the lost point.  The capped lift from the root of the donor face (bountifulness)
is capped at the least designated top concerned at the cells read by the owner at most the
replaced reading of the lost top (`H2.lawfulOne_capBelow`): the lost top is among them, so the
frontier is at most the cap; the root top cells are read strictly above (the strict source gaps)
and the low root cells are below the cap, so the root is kept. -/
theorem ownerLoweringBelow_oneFace {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g₀ : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g₀.trans Fin.castSuccEmb) l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {p : StageType.{u} α 1} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α 2} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    {A : Set (Fin p.card)}
    (hA : ∀ a ∈ A, p.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope (StageType.faceCell hp a))
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A) :
    OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r 1 (LawfulOne t')
      (LawfulOne tb) Lo Tops := by
  classical
  intro h hh L g hL hg hagr
  obtain ⟨W1, hW1, hW1r, hW1L⟩ := hasCappedLifts_lawfulOne_one htbleg htbp hleg hp hh hL hg
    (fun x ↦ hagr x)
  set S := Tops.filter fun t ↦ h ≤ g t ∧ visibilityReplace 1 1 (Lo.sup g) < g t with hSdef
  by_cases hSne : S.Nonempty
  swap
  · refine ⟨W1, hW1, hW1r, hW1L, fun t ht hht hlt ↦ ?_⟩
    exact absurd ⟨t, mem_filter.mpr ⟨ht, hht, hlt⟩⟩ hSne
  set c := S.inf' hSne g with hcdef
  obtain ⟨t₀, ht₀, hct₀⟩ := Finset.exists_mem_eq_inf' hSne g
  obtain ⟨-, hht₀, hlt₀⟩ := mem_filter.mp ht₀
  have hct : c = g t₀ := hct₀
  have hc0 : ⊥ < c := by rw [hct]; exact bot_le.trans_lt hlt₀
  have hcS (t : Fin tb.card) (ht : t ∈ Tops) (hht : h ≤ g t)
      (hlt : visibilityReplace 1 1 (Lo.sup g) < g t) : c ≤ g t :=
    Finset.inf'_le g (mem_filter.mpr ⟨ht, hht, hlt⟩)
  -- the cap is self-visible at `1`: the designated top `t₀` has grade `1`
  have hc : IsSelfVisible 1 c := by
    have hg1 : tb.toCellScheme.grade t₀ ≤ 1 := by
      by_contra hgt
      have := hg.2 t₀ hgt
      rw [this] at hlt₀
      exact not_lt_bot hlt₀
    have hgt1 : tb.toCellScheme.grade t₀ = 1 :=
      le_antisymm hg1 (tb.isWellFormed.isWellFormed.grade_pos t₀)
    have := (Rows.isLawfulBelow_iff_forall.mp hg.1).1 t₀ ⟨subset_univ _, hg1⟩
    rw [hgt1] at this
    rw [hct]
    exact this
  have hhc : h ≤ c := le_inf' hSne g fun t ht ↦ (mem_filter.mp ht).2.1
  have hLoc : Lo.sup g < c := by
    rw [hct]
    exact (le_visibilityReplace (k := 1) (i := 1) (by omega) _).trans_lt hlt₀
  refine ⟨capBelow t' o r W1 c, lawfulOne_capBelow hleg hs honly hW1 hc hc0, fun x ↦ ?_,
    fun d ↦ ?_, fun t ht hht hlt ↦ ?_⟩
  · -- the root is kept
    by_cases hZ : t'.rowAt o (StageType.faceCell hp x) ≤ threshold t' o r
    · rw [capBelow_of_le hZ, hW1r x]
      refine min_eq_left ?_
      rcases hroot x with hx | hx
      · exact (Finset.le_sup hx).trans hLoc.le
      · exact absurd hZ (not_le.mpr (hs.gap_retained _
          ((StageType.label_faceCell hp x).trans (hA x hx).1) (hA x hx).2))
    · rw [capBelow_of_not_le hZ, hW1r x]
  · -- agreement capped at `h`
    rw [← hW1L d]
    by_cases hZ : t'.rowAt o d ≤ threshold t' o r
    · rw [capBelow_of_le hZ, min_assoc, min_eq_right hhc]
    · rw [capBelow_of_not_le hZ]
  · -- the frontier is at most the cap
    have hZr : t'.rowAt o r ≤ threshold t' o r := le_visibilityReplace (by omega) _
    refine (min_le_right _ _).trans ?_
    rw [capBelow_of_le hZr, visibilityReplace_min le_rfl, hc.visibilityReplace_eq]
    exact (min_le_right _ _).trans (hcS t ht hht hlt)

/-- **The state admission between the grade-`1` faces at grade `1`**, at a legal context whose
owner is the only cell of its graded index: donor raising with the gap
(`H2.donorRaisingGap_oneFace`) and owner lowering below the designated tops
(`H2.ownerLoweringBelow_oneFace`) in `H2.selfLow_isStateAdmissionGap_of_below`. -/
theorem stateAdmission_oneFace_of_owner {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {p : StageType.{u} α 1} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α 2} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops)
    {A : Set (Fin p.card)}
    (hA : ∀ a ∈ A, p.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope (StageType.faceCell hp a))
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 (LawfulOne t')
      (LawfulOne tb) (SelfLowG o r 1 (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops) := by
  have hroot1 (x : Fin p.card) :
      StageType.faceCell htbp x ∈ Lo.filter (fun x ↦ tb.toCellScheme.grade x ≤ 1) ∨ x ∈ A :=
    (hroot x).imp_left fun h ↦ mem_filter.mpr
      ⟨h, (StageType.grade_faceCell _ x).trans_le (p.grade_le x)⟩
  exact selfLow_isStateAdmissionGap_of_below A
    (fun _ hf ↦ (frontier_le_lawfulOne hleg hs hp hf).1)
    (fun _ hf a ha ↦ (frontier_le_lawfulOne hleg hs hp hf).2 a (hA a ha).1 (hA a ha).2)
    (donorRaisingGap_oneFace hleg hp htbleg htbp hLo hTops hroot)
    (ownerLoweringBelow_oneFace hleg hs honly hp htbleg htbp hA hroot1)

/-- **h2 at two points, top grade `1`, at a context whose owner is alone at its graded index**: the
conclusion of `H2.exists_completion_recProp_one` (on the research branch `research/port-low-padded`)
from the state admission between the grade-`1` faces (`H2.stateAdmission_oneFace_of_owner`,
`H2.exists_completion_recProp_one_of_admission`). -/
theorem exists_completion_recProp_one_of_owner {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    {n : ℕ} {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {p : StageType.{u} α 1} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α 2} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops' : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ 1)
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops)
    {A : Set (Fin p.card)}
    (hA : ∀ a ∈ A, p.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope (StageType.faceCell hp a))
    (hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ A) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 1 Lo Tops :=
  exists_completion_recProp_one_of_admission hleg hs hp htbleg htbp hTops'
    (stateAdmission_oneFace_of_owner hleg hs honly hp htbleg htbp hLo hTops hA hroot)

end VaughtConjecture.H2

/-! ### The two contexts on their grade-`1` faces -/

namespace VaughtConjecture.OwnerGradeOneTop

open Finset StageType H2

/-- The owner `2` is the only cell of its graded index. -/
theorem eq_owner (α : Ordinal.{u}) (u : Fin (ctx α).card)
    (hu : (ctx α).toCellScheme.gradedIndex u = (ctx α).toCellScheme.gradedIndex (cellC α 2)) :
    u = cellC α 2 := by
  have key : ∀ u : Fin 4, OwnerGradeOne.cells.gradedIndex u = OwnerGradeOne.cells.gradedIndex 2 →
      u = 2 := by decide
  exact key u hu

/-- **The clause is an admission of states between the grade-`1` faces** at the context where it
is not one between the full labellings (`OwnerGradeOneTop.not_isStateAdmission_designated`), with
the designation of the clause and the context itself as donor. -/
theorem isStateAdmission_oneFace (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hLo : ∀ x, (ctx α).label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, (ctx α).label x = ⊤ → (ctx α).toCellScheme.grade x ≤ 1 →
      x ∉ (ctx α).toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet (ctx α) x → x ∈ Tops) :
    IsStateAdmission (faceCell hp) (faceCell hp) 1 (LawfulOne (ctx α)) (LawfulOne (ctx α))
      (SelfLowG (cellC α 2) (cellC α 1) 1
        (Lo.filter fun x ↦ (ctx α).toCellScheme.grade x ≤ 1) Tops) :=
  stateAdmission_oneFace_of_owner (isLegal_ctx α)
    (isSourceGapContextAt_ctx α (Function.Embedding.refl (Fin 1))) (eq_owner α) hp
    (isLegal_ctx α) hp hLo hTops (A := {x | p.label x = ⊤})
    (fun a ha ↦ ⟨ha, by
      rw [faceCell_eq_zero α hp a]
      change (1 : Fin 2) ∉ OwnerGradeOne.cells.scope 0
      decide⟩)
    (fun x ↦ by
      by_cases hx : p.label x = ⊤
      · exact .inr hx
      · exact .inl (hLo _ (by rw [label_faceCell]; exact hx)))

end VaughtConjecture.OwnerGradeOneTop

namespace VaughtConjecture.OwnerGradeOne

open Finset StageType H2

/-- The owner `2` is the only cell of its graded index. -/
theorem eq_owner (α : Ordinal.{u}) (u : Fin (ctx α).card)
    (hu : (ctx α).toCellScheme.gradedIndex u = (ctx α).toCellScheme.gradedIndex (cellC α 2)) :
    u = cellC α 2 := by
  have key : ∀ u : Fin 4, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
  exact key u hu

/-- **The clause is an admission of states between the grade-`1` faces** at the context where
owner lowering between the full labellings fails (`OwnerGradeOne.not_ownerLowering_one`), with the
designation of the clause and the context itself as donor: its root cell, labelled `⊥`, is
designated low. -/
theorem isStateAdmission_oneFace (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hLo : ∀ x, (ctx α).label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, (ctx α).label x = ⊤ → (ctx α).toCellScheme.grade x ≤ 1 →
      x ∉ (ctx α).toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet (ctx α) x → x ∈ Tops) :
    IsStateAdmission (faceCell hp) (faceCell hp) 1 (LawfulOne (ctx α)) (LawfulOne (ctx α))
      (SelfLowG (cellC α 2) (cellC α 1) 1
        (Lo.filter fun x ↦ (ctx α).toCellScheme.grade x ≤ 1) Tops) :=
  stateAdmission_oneFace_of_owner (isLegal_ctx α)
    (isSourceGapContextAt_ctx α (Function.Embedding.refl (Fin 1))) (eq_owner α) hp
    (isLegal_ctx α) hp hLo hTops (A := ∅) (fun _ h ↦ h.elim)
    (fun x ↦ .inl (hLo _ (by rw [faceCell_eq_zero α hp x]; exact fun h ↦ by simp [ctx, lab] at h)))

end VaughtConjecture.OwnerGradeOne

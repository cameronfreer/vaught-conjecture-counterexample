/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeRankMember

/-!
# One level of the values per grade

Roadmap, Layer 3 ((R3) and (R4), one level of the ladder tower with the values per grade), in the
native interfaces: the states of the level, their writing on the base and on one layer, their
capped agreement, and the recoding from the next grade.

* **The states of the level at the grade `k`** are orbit codes `orbitCode k W` of lawful states:
  every field of the attachment is coded, the fields of grade above `k` included, and the state is
  lawful below `(univ, k)` (`CellScheme.Rows.IsLawfulBelow.orbitCode`), with values self-visible at
  `1` (`Label.isSelfVisible_witness_of_le`).
* **The base writing** is `Scheme.LadderBaseData.stateExtOf` with the rank member from the grade
  one: lawful below `(univ, k)` (`Scheme.LadderBaseData.isLawfulBelow_stateExtOf`), equal to
  `stateExt` on lawful states (`Scheme.LadderBaseData.stateExtOf_eq_stateExt`).  Tested at both
  inputs (`TieInstance` at its top grade `2`, `ApexInstance` at `2 < 3`):
  `Seed.isLawfulBelow_stateExtOf_orbitCode`.
* **The rendering of one level** (`Scheme.LadderBaseData.min_stateExtOf_eq`,
  `Scheme.LadderBaseData.min_layerRow_stateExtOf_eq`): two states lawful below `(univ, 1)` agreeing
  capped at `y ≠ ⊥` self-visible at `1` have base writings agreeing capped at `y` at the cells of
  the attachment and the ladder (the rank members agree in rank below the low count), and, at a
  height `y` of the layer, layer rows agreeing capped at `y` at the old and the new cells.
* **The recoding from the grade `k + 3` to `k + 2`** (`Seed.recode_mem`): a state lawful below
  `(univ, k + 3)` and admitted has its orbit code at `k + 2` in the code grid at `k + 2`,
  orbit-canonical, lawful below `(univ, k + 2)`, admitted
  (`Seed.attachAdmits_comp_of_le`, a witness bounded by any grade at least the threshold), and read
  back literally by the orbit decoder at the cut `k + 2` (`Label.min_orbitCode_gridPoint_zero`).

## References

Lawful sections are [Kni26, Definition 2.5.4]; agreement heights are those of the coatom extension
construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

/-- **A witness bounded by `k` keeps self-visibility at every grade `j ≤ k`.** -/
theorem isSelfVisible_witness_of_le {k j : ℕ} (hjk : j ≤ k) {θ : Label.{u} → Label.{u}}
    (hθ : IsWitness (stepSuppressor k) θ) {y : Label.{u}} (hy : IsSelfVisible j y) :
    IsSelfVisible j (θ y) := by
  have h := hθ.visibilityReplace_comm y j (by rw [stepSuppressor_of_le hjk]; exact le_top) j
    le_rfl
  unfold IsSelfVisible at hy ⊢
  rw [hy] at h
  exact h.symm

end Label

namespace Scheme.LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ}

/-- **The rendering of one level on the base**: two states lawful below `(univ, 1)` agreeing
capped at `y ≠ ⊥` self-visible at `1` have extensions with their rank members agreeing capped at
`y`: on the cells of the attachment they are the states; on the ladder the indices of the members
agree up to the low count (`Label.rankAgree_of_min_eq`, `Scheme.baseIndex_agree`) and the positive
tables agree capped at `y` there (`Label.min_posTable_eq`). -/
theorem min_stateExtOf_eq (hcard : B.S.card ≤ H) {y : Label.{u}} (hy0 : y ≠ ⊥)
    (hy1 : IsSelfVisible 1 y) {R R' : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d)
    (hR' : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R' d)
    (hag : ∀ d, min (R' d) y = min (R d) y) (t : Fin (B.ladderBase H).card) :
    min (B.stateExtOf R' (RankMember.ofLawfulBelowOne B.wf hcard hR') t) y =
      min (B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard hR) t) y := by
  induction t using Fin.addCases with
  | left d =>
    change min (Fin.append R' _ (Fin.castAdd _ d)) y = min (Fin.append R _ (Fin.castAdd _ d)) y
    rw [Fin.append_left, Fin.append_left]
    exact hag d
  | right j =>
    change min (Fin.append R' _ (Fin.natAdd _ j)) y = min (Fin.append R _ (Fin.natAdd _ j)) y
    rw [Fin.append_right, Fin.append_right]
    set a := RankMember.ofLawfulBelowOne B.wf hcard hR with ha
    set a' := RankMember.ofLawfulBelowOne B.wf hcard hR' with ha'
    set L := lowCount R y with hL
    have hag' : RankAgree (rankProf B.S H a') (rankProf B.S H a) (L + 1) :=
      rankAgree_of_min_eq hag hy0
    have hcut := baseIndex_agree (H := H) (prof := rankProf B.S H) a' a (Fin.natAdd _ j)
    have hle (b : RankMember B.S H) : baseIndex H (rankProf B.S H) b (Fin.natAdd _ j) ≤ H :=
      baseIndex_le (rankProf_le _ H) b _
    refine min_posTable_eq hag (one_le_of_isSelfVisible hy1 hy0) ?_
    rcases le_or_gt (L + 1) H with hLH | hLH
    · have hc : L + 1 ≤ rankCut H (rankProf B.S H a') (rankProf B.S H a) := le_rankCut hLH hag'
      have e := congrArg (min · (L + 1)) hcut
      simp only [min_assoc, min_eq_right hc] at e
      exact e
    · have hc : H ≤ rankCut H (rankProf B.S H a') (rankProf B.S H a) :=
        le_rankCut le_rfl (hag'.mono hLH.le)
      rw [min_eq_left ((hle a').trans hc), min_eq_left ((hle a).trans hc)] at hcut
      rw [hcut]

/-- **The rendering of one level on one layer**: over the base writings of two states as in
`Scheme.LadderBaseData.min_stateExtOf_eq`, the layer rows of any catalogue of entries with
agreement heights in a set `G` containing `⊥` and `y` agree capped at `y` at every cell, old and
new (`Scheme.min_layerRow_eq`). -/
theorem min_layerRow_stateExtOf_eq (hcard : B.S.card ≤ H) {y : Label.{u}} (hy0 : y ≠ ⊥)
    (hy1 : IsSelfVisible 1 y) {R R' : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d)
    (hR' : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R' d)
    (hag : ∀ d, min (R' d) y = min (R d) y) {G : Finset Label.{u}} (hG0 : ⊥ ∈ G) (hyG : y ∈ G)
    {E : Finset (Fin (B.ladderBase H).card → Label.{u})}
    (x : Fin ((B.ladderBase H).card + E.card)) :
    min (layerRow (B.ladderBase H) (fun d ↦ d) G E
      (B.stateExtOf R' (RankMember.ofLawfulBelowOne B.wf hcard hR')) x) y =
      min (layerRow (B.ladderBase H) (fun d ↦ d) G E
        (B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard hR)) x) y :=
  Scheme.min_layerRow_eq hG0 hyG (min_stateExtOf_eq hcard hy0 hy1 hR hR' hag) x

end Scheme.LadderBaseData

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-- **The states of a level are written lawfully below their grade**: the orbit code at a grade
`k ≥ 1` of a lawful state of the attachment has values self-visible at `1`, is lawful below
`(univ, k)`, and its extension with the rank member from the grade one is lawful below
`(univ, k)`. -/
theorem isLawfulBelow_stateExtOf_orbitCode {H : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ} (hk : 1 ≤ k)
    {W : Fin (I.attachment g).card → Label.{u}} (hW : (I.attachment g).rows.IsLawful W) :
    ∃ hP : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
        (fun d ↦ orbitCode k W d),
      (I.attachmentBase g).ladderBase H |>.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
        fun t ↦ (I.attachmentBase g).stateExtOf (orbitCode k W)
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard
            (hP.mono (show ((univ : Finset (Fin (m + 2))), 1) ≤
              ((univ : Finset (Fin (m + 2))), k) from ⟨subset_rfl, hk⟩))) t := by
  have hP : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
      (fun d ↦ orbitCode k W d) := (hW.isLawfulBelow _).orbitCode fun d ↦ d.2.2
  have hv1 (e : Fin (I.attachment g).card) : IsSelfVisible 1 (orbitCode k W e) :=
    Label.isSelfVisible_witness_of_le hk (isWitness_orbitMap k W)
      ((I.attachmentBase g).isSelfVisible_one_of_isLawful hW e)
  exact ⟨hP, Scheme.LadderBaseData.isLawfulBelow_stateExtOf hH hcard hk hP hv1⟩

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **Admission is carried by a witness bounded by any grade at least the threshold**, sending
only `⊥` to `⊥` on the values of the state. -/
theorem attachAdmits_comp_of_le
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {K₀ K : ℕ}
    (hK₀ : Q.threshold ≤ K₀) (hK : Q.threshold ≤ K)
    {P : Fin (I.attachment g).card → Label.{u}} (hPA : I.attachAdmits g hd Q K₀ P)
    {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor K) ν)
    (hbot : ∀ a, ν (P a) = ⊥ ↔ P a = ⊥) (K' : ℕ) : I.attachAdmits g hd Q K' (ν ∘ P) := by
  intro _ hcls hcap j
  have hhat (a : Fin (I.attachment g).card) :
      I.attachHatAt g Q.threshold (ν ∘ P) a = ν (I.attachHatAt g Q.threshold P a) :=
    attachHatAt_comp hν.map_bot _ P a
  have hhbot (a : Fin (I.attachment g).card) :
      ν (I.attachHatAt g Q.threshold P a) = ⊥ ↔ I.attachHatAt g Q.threshold P a = ⊥ := by
    unfold attachHatAt
    split_ifs
    · exact hbot a
    · exact ⟨fun _ ↦ rfl, fun _ ↦ hν.map_bot⟩
  have hP := hPA hK₀ (fun x hx ↦ by
      have h := hcls x hx
      simp only [hhat] at h
      exact (hhbot _).symm.trans h)
    (fun h0 ↦ hcap (by
      simp only [hhat]
      exact (hhbot _).mpr h0)) j
  have hθv : ∀ i ≤ Q.threshold, ∀ x, ν (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (ν x) := fun i hi x ↦
    hν.visibilityReplace_comm x _ (by rw [stepSuppressor_of_le hK]; exact le_top) i hi
  have hmap := hP.map hν.monotone hν.map_bot hθv (fun hf ↦ (hQ.ref j hf).2.1) hQ.marker.2.1
  have e1 : (fun x ↦ I.attachHatAt g Q.threshold (ν ∘ P) (I.attachCtxCell g x)) =
      ν ∘ fun x ↦ I.attachHatAt g Q.threshold P (I.attachCtxCell g x) := funext fun x ↦ hhat _
  change Q.CorrectAt (fun x ↦ I.attachHatAt g Q.threshold (ν ∘ P) (I.attachCtxCell g x)) j
    (I.attachHatAt g Q.threshold (ν ∘ P) (I.attachDonCell g hd j))
  rw [e1, hhat]
  exact hmap

/-- **The recoding from the grade `k + 3` to the grade `k + 2`**: a state of the attachment lawful
below `(univ, k + 3)` and admitted at `k + 3` has its orbit code at `k + 2` in the code grid at
`k + 2` (bound `B ≥ 2 * #F`), orbit-canonical, lawful below `(univ, k + 2)`, admitted at every
grade, and read back literally by the orbit decoder at the cut `k + 2`, a witness bounded by
`k + 2`.  When the threshold exceeds `k + 2` the admission at `k + 2` is vacuous; the admission at
the higher grades is carried by the orbit map when the threshold is at most `k + 2`. -/
theorem recode_mem {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k B : ℕ}
    (hB : 2 * (I.attachment g).card ≤ B) {P : Fin (I.attachment g).card → Label.{u}}
    (hPl : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k + 3)
      fun d ↦ P d)
    (hPA : I.attachAdmits g hd Q (k + 3) P) :
    (∀ a, orbitCode (k + 2) P a ∈ codeGrid (k + 2) B) ∧
      orbitCode (k + 2) (orbitCode (k + 2) P) = orbitCode (k + 2) P ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k + 2)
        (fun d ↦ orbitCode (k + 2) P d) ∧
      I.attachAdmits g hd Q (k + 2) (orbitCode (k + 2) P) ∧
      IsWitness (stepSuppressor (k + 2)) (orbitDecoder (k + 2) P (gridPoint (k + 2) 0)) ∧
      ∀ a, orbitDecoder (k + 2) P (gridPoint (k + 2) 0) (orbitCode (k + 2) P a) = P a := by
  have hX : ((univ : Finset (Fin (m + 2))), k + 2) ≤ ((univ : Finset (Fin (m + 2))), k + 3) :=
    ⟨subset_rfl, by omega⟩
  have hgv : IsSelfVisible (k + 2) (gridPoint.{u} (k + 2) 0) :=
    isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) le_rfl
  have hg0 : gridPoint.{u} (k + 2) 0 ≠ ⊥ := WithBot.coe_ne_bot
  refine ⟨fun a ↦ orbitMap_mem_codeGrid (by simpa using hB) _, orbitCode_orbitCode,
    (hPl.mono hX).orbitCode fun d ↦ d.2.2, fun hk ↦ ?_, isWitness_orbitDecoder hgv hg0,
    orbitDecoder_orbitCode fun a ↦ min_orbitCode_gridPoint_zero a⟩
  exact attachAdmits_comp_of_le hd hQ (by omega) hk hPA (isWitness_orbitMap (k + 2) P)
    (fun _ ↦ orbitMap_eq_bot_iff) (k + 2) hk

end Seed

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **The level at the top grade `2` of the tie input**: the orbit code at `2` of the compressed
labelling is lawful below `(univ, 2)`, and so is its extension with the rank member from the grade
one. -/
theorem isLawfulBelow_stateExtOf_two {α : Ordinal.{u}} (I : Seed.{u} α 1) :
    ∃ hP : (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ orbitCode 2 (I.compressedLabel 𝕣) d),
      (I.attachmentBase 𝕣).ladderBase (I.seedHeight 𝕣) |>.rows.IsLawfulBelow
        ((univ : Finset (Fin 3)), 2) fun t ↦ (I.attachmentBase 𝕣).stateExtOf
          (orbitCode 2 (I.compressedLabel 𝕣))
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase 𝕣).wf (I.card_le_seedHeight 𝕣)
            (hP.mono (show ((univ : Finset (Fin 3)), 1) ≤ ((univ : Finset (Fin 3)), 2) from
              ⟨subset_rfl, by omega⟩))) t :=
  Seed.isLawfulBelow_stateExtOf_orbitCode (I.seedHeight_pos 𝕣) (I.card_le_seedHeight 𝕣)
    (by omega) (Seed.isLawful_compressedLabel (I := I) (g := 𝕣))

end TieInstance

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- **The level at the grade `2 < 3` of the input with an apex**: the orbit code at `2` of the
compressed labelling, not lawful (`ApexInstance.not_isLawful_orbitCode_two`), is lawful below
`(univ, 2)`, and so is its extension with the rank member from the grade one. -/
theorem isLawfulBelow_stateExtOf_two {α : Ordinal.{u}} (I : Seed.{u} α 2) :
    ∃ hP : (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2)
        (fun d ↦ orbitCode 2 (I.compressedLabel 𝕘) d),
      (I.attachmentBase 𝕘).ladderBase (I.seedHeight 𝕘) |>.rows.IsLawfulBelow
        ((univ : Finset (Fin 4)), 2) fun t ↦ (I.attachmentBase 𝕘).stateExtOf
          (orbitCode 2 (I.compressedLabel 𝕘))
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase 𝕘).wf (I.card_le_seedHeight 𝕘)
            (hP.mono (show ((univ : Finset (Fin 4)), 1) ≤ ((univ : Finset (Fin 4)), 2) from
              ⟨subset_rfl, by omega⟩))) t :=
  Seed.isLawfulBelow_stateExtOf_orbitCode (I.seedHeight_pos 𝕘) (I.card_le_seedHeight 𝕘)
    (by omega) (Seed.isLawful_compressedLabel (I := I) (g := 𝕘))

end ApexInstance

end VaughtConjecture

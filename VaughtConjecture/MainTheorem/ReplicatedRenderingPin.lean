/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedPinInstance
import VaughtConjecture.MainTheorem.ReplicatedRenderingChoice

/-!
# Cap-compatible rendering fails at the pinned seed

Roadmap, Layer 3 ((R3) and (R4), the rendering of states in the replicated scheme).

**At the seed position** (`StageType.CapCompatibleRenderingAtSeed`): cap-compatible rendering
(`Seed.CapCompatibleRendering`) at every seed position, every grade `2 ≤ j ≤ m + 1`, for the
admission predicate of the requests.

**Glued states** (`Seed.not_capCompatibleRendering_of_glued_split`): lawful sections of the context
and of the donor agreeing on the root glue to two states of the catalogue
(`StageType.exists_joint_extension`), both admitted off the exact class; if they agree capped at
`c` and are separated at a context cell with no height between `c` and the smaller of their values
there, the rendering fails (`Seed.not_capCompatibleRendering_of_split`, identity decoders).

**Realized** (`StageType.not_capCompatibleRenderingAtSeed_seedChoice`): at the input of
`StageType.not_towerExtensionPosAtSeed_seedChoice` (stage `ω`, `m = n = 1`, the legal context
`PinInstance.ctxP`, the donor `PinInstance.donP`, the bottom requests `PinInstance.reqP`, the
grade `2`, the cap `N` above every finite value of the choice), the ambient state and the
prescription of the pin are both states of the catalogue at `m + 2`, agreeing capped at `N`.
At the layer cell of the prescription its own writing is the top of the height set, and the
ambient's writing is their agreement height, at most `ω + 1 < N` (`PinInstance.pin_heightSet`).
So the two canonical writings, decoded by the identity, disagree capped at `N`.  The failure is
the pin itself seen on two writings: above a cap with no representative among the heights the
layer cells are selected by heights, and a height at most `ω + 1` reads below the cap.

## References

Lawful sections are [Kni26, Definition 2.5.4]; agreement heights are those of the coatom
extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {B' : ℕ}

/-- **Two glued states separated above a cap that is not a height defeat cap-compatible
rendering**: lawful sections `uR`, `uP` of the context and `wR`, `wP` of the donor agreeing on the
root glue to states `R`, `P` with values in `Γ`, admitted off the exact class at a cell `x₀` below
the cap labelled `⊥`; if `P` and `R` agree capped at `c` and differ at a context cell `xa` with no
height of the grade `k + 2 ≤ j` between `c` and the smaller of their values there, cap-compatible
rendering at `j` fails. -/
theorem not_capCompatibleRendering_of_glued_split (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p : StageType.{u} α n} (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p)
    {d : StageType.{u} α (n + 1)} (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte) {j k : ℕ} (hkj : k + 2 ≤ j)
    (hkm : k + 1 ≤ m)
    {uR uP : Fin t'.card → Label.{u}} (huR : t'.rows.IsLawful uR) (huP : t'.rows.IsLawful uP)
    {wR wP : Fin d.card → Label.{u}} (hwR : d.rows.IsLawful wR) (hwP : d.rows.IsLawful wP)
    (hrR : ∀ i, wR (d.faceCell hdp i) = uR (t'.faceCell hte i))
    (hrP : ∀ i, wP (d.faceCell hdp i) = uP (t'.faceCell hte i))
    (hΓuR : ∀ x, uR x ∈ Γ) (hΓwR : ∀ y, wR y ∈ Γ) (hΓuP : ∀ x, uP x ∈ Γ) (hΓwP : ∀ y, wP y ∈ Γ)
    {x₀ : Fin t'.card} (hx₀ : x₀ ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap))
    (hx₀l : t'.label x₀ = ⊥) (hR0 : uR x₀ ≠ ⊥) (hP0 : uP x₀ ≠ ⊥) {c : Label.{u}}
    (hc : IsSelfVisible j c) (hcu : ∀ x, min (uP x) c = min (uR x) c)
    (hcw : ∀ y, min (wP y) c = min (wR y) c) {xa : Fin t'.card} (hne : uP xa ≠ uR xa)
    (hgap : ∀ x ∈ Scheme.heightSet Γ B' (k + 2), c ≤ x → min (uP xa) (uR xa) < x) :
    ¬ I.CapCompatibleRendering g H Γ (I.attachAdmits g hdA (hI ▸ Q)) B' j := by
  subst hI
  have h₁ := I.restrictFace_left_attachmentType g
  have h₂ := I.restrictFace_donor_attachmentType g hdA
  obtain ⟨R, hR, hR1, hR2⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) huR hwR hrR
  obtain ⟨P, hP, hP1, hP2⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) huP hwP hrP
  have hcases (C : Fin (I.attachmentType g).card → Prop)
      (h1 : ∀ x, C ((I.attachmentType g).faceCell h₁ x))
      (h2 : ∀ y, C ((I.attachmentType g).faceCell h₂ y)) (a) : C a := by
    rcases I.attachment_cover g a with ha | ha
    · obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq h₁ ha; exact h1 x
    · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq h₂ ha; exact h2 y
  have hadm {S : Fin (I.attachmentType g).card → Label.{u}}
      (hS1 : S ((I.attachmentType g).faceCell h₁ x₀) ≠ ⊥) :
      I.attachAdmits g hdA Q (m + 2) S :=
    attachAdmits_of_admitsOnClass hdA hQ (m + 2) fun hcls _ ↦
      absurd ((hcls x₀ hx₀).mpr hx₀l) hS1
  have hRmem : R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hdA Q) (m + 2) :=
    Scheme.LadderBaseData.mem_towerCat.mpr ⟨hcases (fun a ↦ R a ∈ Γ)
      (fun x ↦ (hR1 x).symm ▸ hΓuR x) (fun y ↦ (hR2 y).symm ▸ hΓwR y), hR,
      hadm (by rw [hR1]; exact hR0)⟩
  have hPmem : P ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hdA Q) (m + 2) :=
    Scheme.LadderBaseData.mem_towerCat.mpr ⟨hcases (fun a ↦ P a ∈ Γ)
      (fun x ↦ (hP1 x).symm ▸ hΓuP x) (fun y ↦ (hP2 y).symm ▸ hΓwP y), hP,
      hadm (by rw [hP1]; exact hP0)⟩
  refine not_capCompatibleRendering_of_split (R := P) (R' := R) hcard hΓ
    (fun k S h ↦ I.attachAdmits_succ g hdA Q k S h) hkj hkm hc hPmem hRmem
    (hcases (fun a ↦ min (P a) c = min (R a) c) (fun x ↦ by rw [hP1, hR1]; exact hcu x)
      fun y ↦ by rw [hP2, hR2]; exact hcw y)
    (a := (I.attachmentType g).faceCell h₁ xa) (by rw [hP1, hR1]; exact hne) ?_
  intro x hx hcx
  rw [hP1, hR1]
  exact hgap x hx hcx

end Seed

namespace StageType

/-- **Cap-compatible rendering at the seed position**, for a choice of height, values and grid
bound per seed: at every seed position, with the admission predicate of the requests, at every
grade `2 ≤ j ≤ m + 1`. -/
def CapCompatibleRenderingAtSeed
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → I.left.IsLegal →
    restrictFace Fin.castSuccEmb I.left = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces)
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d), 0 < n →
      ∀ Q : GrowthRequests I.left d.toScheme,
        (∀ j, Q.CorrectAt I.left.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∀ j, 2 ≤ j → j ≤ m + 1 →
          Seed.CapCompatibleRendering I g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g) j

open PinInstance SeparationObstruction TieInstance

/-- **Cap-compatible rendering at the seed position read at one seed position**, with the first
coatom type given up to equality. -/
theorem capCompatibleRendering_of_atSeed
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    (h : CapCompatibleRenderingAtSeed.{u} H Γ B') {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    {n m : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m) {t' : StageType.{u} α (m + 1)}
    (hI : I.left = t') {p' : StageType.{u} α m}
    (hp' : restrictFace Fin.castSuccEmb t' = some p') {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ p.cofaces)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) (j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m + 1) :
    Seed.CapCompatibleRendering I g (H I g) (Γ I g) (I.attachAdmits g hdA (hI ▸ Q)) (B' I g) j := by
  subst hI
  exact h I g p' hα I.isLegal_left hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm

/-- **Cap-compatible rendering fails at the choice of the assembly**, at the input of the pin
(`StageType.not_towerExtensionPosAtSeed_seedChoice`): the ambient state (`ω + 1` at the context's
`y`, `z`; `ω + 2` at the donor's `y`, `z`, `o`, `r`) and the prescription (`ω · 2 + 1` at the
context's `y`, `z`; `ω + 2`, `ω + 2`, `ω + 2`, `ω · 2 + 2` at the donor's) are states of the
catalogue at `m + 2` agreeing capped at `N`; at the grade `2` the layer cell of the prescription
reads its own writing at the top of the height set and the ambient's at a height at most
`ω + 1 < N`. -/
theorem not_capCompatibleRenderingAtSeed_seedChoice :
    ¬ CapCompatibleRenderingAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := by
  intro h
  have hα : Order.IsSuccLimit (ω : Ordinal.{u}) := Ordinal.isSuccLimit_omega0
  have hp : restrictFace (Function.Embedding.refl (Fin 1)) (pt1 ω) = some (pt1 ω) :=
    (restrictFace_trans (ctxP ω) _ _ (restrictFace_ctxP ω)).trans (restrictFace_ctxP_root ω)
  obtain ⟨I, hI, hdA⟩ := exists_growthSeed_of_isSuccLimit hα (t' := ctxP ω) (isLegal_ctxP ω)
    (restrictFace_ctxP ω) hp (donP_mem_cofaces ω)
  set g := Function.Embedding.refl (Fin 1) with hg
  have key := capCompatibleRendering_of_atSeed h hα I g hI (restrictFace_ctxP ω)
    (restrictFace_ctxP_root ω) (donP_mem_cofaces ω) hdA Nat.one_pos (reqP ω) (correctAt_reqP ω)
    (classCalibrated_reqP ω) (hasRelativeLiftOnClass_reqP ω) 2 le_rfl le_rfl
  set N := (I.seedValues g).sup labelFinNat + 3 with hN
  -- two distinct cells of the context, so two cells of the attachment at least
  have hC : 2 ≤ (I.attachment g).card := by
    have hne : cellC ω 0 ≠ cellC ω 4 := fun h' ↦ by
      have := grade_cellC ω 0
      rw [h', grade_cellC] at this
      exact absurd this (by decide)
    have h2 : 2 ≤ (ctxP ω).card := by
      by_contra hlt
      exact hne (Fin.ext (by have := (cellC ω 0).2; have := (cellC ω 4).2; omega))
    have hinj := Fintype.card_le_of_injective (I.attachCtxCell g)
      (Scheme.faceCell_injective (I.comap_left_attachment_scheme g))
    simp only [Fintype.card_fin] at hinj
    rw [hI] at hinj
    omega
  have hY : valY ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 1) (f := 1) (by omega) (by omega))
  have hZ : valZ ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 1) (f := 2) (by omega) (by omega))
  have h12 : gridPoint 1 2 ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 2) (f := 1) hC (by omega))
  have h22 : gridPoint 2 2 ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 2) (f := 2) hC (by omega))
  have h0Γ := I.bot_mem_seedValues g
  have hcY : gridPoint N 0 ≤ valY := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hcZ : gridPoint N 0 ≤ valZ := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hc12 : gridPoint N 0 ≤ gridPoint 1 2 := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hc22 : gridPoint N 0 ≤ gridPoint 2 2 := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hYlt : valY < gridPoint 1 2 := gridPoint_lt_gridPoint_iff_lex.mpr (.inl (by omega))
  refine Seed.not_capCompatibleRendering_of_glued_split (I.card_le_seedHeight g)
    (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx) hI (restrictFace_ctxP_root ω)
    (donP_mem_cofaces ω).2 hdA (classCalibrated_reqP ω) (k := 0) le_rfl le_rfl
    (isLawful_ambCtx ω) (isLawful_preCtx ω) (isLawful_ambDon ω) (isLawful_preDon ω)
    (root_amb ω) (root_pre ω) (fun x ↦ lab_mem hY h0Γ h0Γ h0Γ _)
    (fun y ↦ lab_mem hZ hZ hZ h0Γ _) (fun x ↦ lab_mem h12 h0Γ h0Γ h0Γ _)
    (fun y ↦ lab_mem hZ hZ h22 h0Γ _) (x₀ := cellC ω 0)
    (GrowthRequests.mem_below_cap (reqP ω) (classCalibrated_reqP ω).scope_cap
      (((ctxP ω).grade_le _).trans_eq (threshold_reqP ω).symm))
    (by rw [label_ctxP]; rfl) (by rw [ambCtx, faceCell_cellC]; exact gridPoint_ne_bot 1 1)
    (by rw [preCtx, faceCell_cellC]; exact gridPoint_ne_bot 1 2) (c := gridPoint N 0)
    ((isSelfVisible_gridPoint N 0).mono (by omega))
    (fun x ↦ min_lab_eq (by rw [min_eq_right hc12, min_eq_right hcY]) rfl rfl _)
    (fun y ↦ min_lab_eq rfl rfl (by rw [min_eq_right hc22, min_eq_right hcZ]) _)
    (xa := cellC ω 0) ?_ ?_ key
  · rw [preCtx, ambCtx, faceCell_cellC]
    exact hYlt.ne'
  · intro x hx hcx
    rw [preCtx, ambCtx, faceCell_cellC]
    change min (gridPoint 1 2) valY < x
    rw [min_eq_right hYlt.le]
    exact pin_heightSet _ _ x hx hcx

end StageType

end VaughtConjecture

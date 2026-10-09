/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedTieInstance

/-!
# A pin at the seed position: the extension over the tower fails for the repaired scheme

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap at the seed
position, with agreement heights in `Scheme.heightSet`).

**The glued pin** (`Seed.not_towerExtensionPos_of_glued_pin`): lawful sections of the context and
of the donor agreeing on the root glue to an ambient state of the catalogue and a prescription
over the attachment (`StageType.exists_joint_extension`); off the exact class (a positive value at
a cell below the cap labelled `⊥`) both are admitted for bottom-class requests; a pin of the
ambient at a context cell, reversed by the prescription against two donor cells, refutes the
extension over the tower at a positive cap (`Seed.not_towerExtensionPos_of_pin`, the ambient
read literally).

**The input** (namespace `PinInstance`; stage `ω`, `m = n = 1`, every premise of
`StageType.TowerExtensionPosAtSeed` instantiated):

* the context `ctxP`: the legal scheme `SeparationObstruction.S` with its two points exchanged
  (`StageType.reindex`, legality by `StageType.IsLegal.reindex`), labelled `⊤` at `r` and `⊥`
  elsewhere: the dead cell `e` on the root point `0`, the free cell `y` on the point `1`;
* the root `{0}` with the face `pt1` (the dead cell), the donor `donP` (the same scheme labelled
  `⊥`, a legal coface of `pt1`), the seed of `StageType.exists_growthSeed_of_isSuccLimit`;
* the bottom requests `reqP` (cap and marker `r`), with the labels pair admitted, calibrated on
  the class, with the relative lift on the exact class
  (`StageType.GrowthRequests.hasRelativeLiftOnClass_of_bottoms`);
* the grade `2 = m + 1`; the cap `N = sup (finite parts of the values of the choice) + 3`, a
  natural number, self-visible at `2`, not a height;
* the ambient state: `ω + 1` at the context's `y`, `z`; `ω + 2` at the donor's `y`, `z`, `o`, `r`
  (values of the code set); the prescription: `ω · 2 + 1` at the context's `y`, `z`; `ω + 2` at
  the donor's `y`, `z`, `o` and `ω · 2 + 2` at its `r`; they agree capped at `N` (every positive
  value lies above `N`), and both are admitted (off the exact class at the context's `y`).

The pin (`PinInstance.pin_heightSet`): every height at `2` at least `N` lies above `ω + 1`; the
context's `y` carries `ω + 1` in the ambient.  The serving cell of the donor's `r` reads the
context's `y` at `ω + 1` and the donor's `y` at least that, while the prescription orders them
`ω + 2 < ω · 2 + 1`.

**Conclusions** (`StageType.not_towerExtensionPosAtSeed_seedChoice`,
`StageType.not_towerExtensionAtSeed_seedChoice`): for the repaired scheme, at the choice of the
assembly, the extension over the tower and its case at a positive cap at the seed position are
false.  This refutes these two statements, which quantify over every admitted complete state of
the attachment (the donor cells included).  It does not refute the context lift
(`StageType.HasContextLiftAtSeed`, whose prescription lies below the context coatom; the donor
values of the lift are free), nor `StageType.HasReplicatedInputsAtSeed`, nor the main theorem.
The cap used has no representative in the height set (`Seed.cap_not_mem_heightSet_of_pin`); the
cells that may serve above it are selected by the ambient's own values, heights
(`Seed.replicatedWriting_castAdd_mem_heightSet`), whatever decoder a lift uses.

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14]; the growth
construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {B' : ℕ}

/-- **A pin glued from the faces of the attachment defeats the extension over the tower at a
positive cap**, for the admission predicate of bottom-class requests: lawful sections `uR`, `uP`
of the context and `wR`, `wP` of the donor agreeing on the root glue to an ambient state `R'`
(values in `Γ`) and a prescription `P` (`StageType.exists_joint_extension`); both are admitted,
being off the exact class at a cell `x₀` below the cap labelled `⊥`; and a pin of `R'` at a
context cell `xa` reversed by `P` against two donor cells refutes the extension
(`Seed.not_towerExtensionPos_of_pin`, the ambient read literally). -/
theorem not_towerExtensionPos_of_glued_pin (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    {t' : StageType.{u} α (m + 1)} (hI : I.left = t') {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) {d : StageType.{u} α (n + 1)}
    (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte) {j k : ℕ} (hk2 : 2 ≤ k)
    (hkj : k ≤ j) (hjm : j ≤ m + 1)
    {uR uP : Fin t'.card → Label.{u}} (huR : t'.rows.IsLawful uR) (huP : t'.rows.IsLawful uP)
    {wR wP : Fin d.card → Label.{u}} (hwR : d.rows.IsLawful wR) (hwP : d.rows.IsLawful wP)
    (hrR : ∀ i, wR (d.faceCell hdp i) = uR (t'.faceCell hte i))
    (hrP : ∀ i, wP (d.faceCell hdp i) = uP (t'.faceCell hte i))
    (hΓu : ∀ x, uR x ∈ Γ) (hΓw : ∀ y, wR y ∈ Γ) {x₀ : Fin t'.card}
    (hx₀ : x₀ ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap))
    (hx₀l : t'.label x₀ = ⊥) (hR0 : uR x₀ ≠ ⊥) (hP0 : uP x₀ ≠ ⊥) {c : Label.{u}}
    (hc : IsSelfVisible j c) (hc0 : c ≠ ⊥) (hcu : ∀ x, min (uP x) c = min (uR x) c)
    (hcw : ∀ y, min (wP y) c = min (wR y) c) {xa : Fin t'.card} {y₁ y₃ : Fin d.card}
    (hxa : t'.toCellScheme.grade xa ≤ k) (hy₁ : d.toCellScheme.grade y₁ ≤ k)
    (hy₃ : d.toCellScheme.grade y₃ = k) (hle : uR xa ≤ wR y₁)
    (hpin : ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ x → uR xa < x) (h13 : uP xa ≤ wP y₃)
    (h1 : wP y₁ < uP xa) (hc3 : ¬ wP y₃ ≤ c) :
    ¬ TowerExtensionPos I g H Γ (I.attachAdmits g hdA (hI ▸ Q)) B' j := by
  subst hI
  have h₁ := I.restrictFace_left_attachmentType g
  have h₂ := I.restrictFace_donor_attachmentType g hdA
  obtain ⟨R, hR, hR1, hR2⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) huR hwR hrR
  obtain ⟨P, hP, hP1, hP2⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) huP hwP hrP
  -- every cell of the attachment is a cell of the context or of the donor
  have hcases (C : Fin (I.attachmentType g).card → Prop)
      (h1 : ∀ x, C ((I.attachmentType g).faceCell h₁ x))
      (h2 : ∀ y, C ((I.attachmentType g).faceCell h₂ y)) (a) : C a := by
    rcases I.attachment_cover g a with ha | ha
    · obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq h₁ ha; exact h1 x
    · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq h₂ ha; exact h2 y
  -- admission off the exact class
  have hadm {S : Fin (I.attachmentType g).card → Label.{u}}
      (hS1 : S ((I.attachmentType g).faceCell h₁ x₀) ≠ ⊥) :
      I.attachAdmits g hdA Q (m + 2) S :=
    attachAdmits_of_admitsOnClass hdA hQ (m + 2) fun hcls _ ↦
      absurd ((hcls x₀ hx₀).mpr hx₀l) hS1
  have hRmem : R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hdA Q) (m + 2) :=
    Scheme.LadderBaseData.mem_towerCat.mpr ⟨hcases (fun a ↦ R a ∈ Γ)
      (fun x ↦ (hR1 x).symm ▸ hΓu x) (fun y ↦ (hR2 y).symm ▸ hΓw y), hR,
      hadm (by rw [hR1]; exact hR0)⟩
  refine not_towerExtensionPos_of_pin (σ := id) (c := c) (R' := R) (P := P) hH hcard hΓ
    (fun k S h ↦ I.attachAdmits_succ g hdA Q k S h) hk2 hkj hjm hRmem (IsWitness.id_step j)
    (fun _ h ↦ h) hc hc0 hP (hadm (by rw [hP1]; exact hP0))
    (fun a _ ↦ hcases (fun a ↦ min (P a) c = min (id (R a)) c)
      (fun x ↦ by rw [hP1, id, hR1]; exact hcu x) (fun y ↦ by rw [hP2, id, hR2]; exact hcw y) a)
    (a := (I.attachmentType g).faceCell h₁ xa) (a₁ := (I.attachmentType g).faceCell h₂ y₁)
    (a₃ := (I.attachmentType g).faceCell h₂ y₃)
    ((StageType.grade_faceCell h₁ xa).trans_le hxa) ((StageType.grade_faceCell h₂ y₁).trans_le hy₁)
    ((StageType.grade_faceCell h₂ y₃).trans hy₃) (by rw [hR1, hR2]; exact hle)
    (fun x hx hcx ↦ by rw [hR1]; exact hpin x hx hcx) (by rw [hP1, hP2]; exact h13)
    (by rw [hP1, hP2]; exact h1) (by rw [hP2]; exact hc3)

end Seed

namespace StageType

/-- **The extension over the tower at a positive cap at the seed position read at one seed
position**, with the first coatom type given up to equality. -/
theorem towerExtensionPos_of_atSeed
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    (h : TowerExtensionPosAtSeed.{u} H Γ B') {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    {n m : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m) {t' : StageType.{u} α (m + 1)}
    (hI : I.left = t') {p' : StageType.{u} α m}
    (hp' : restrictFace Fin.castSuccEmb t' = some p') {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ p.cofaces)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) (j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m + 1) :
    Seed.TowerExtensionPos I g (H I g) (Γ I g) (I.attachAdmits g hdA (hI ▸ Q)) (B' I g) j := by
  subst hI
  exact h I g p' hα I.isLegal_left hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm

end StageType

namespace PinInstance

open SeparationObstruction TieInstance

/-- The exchange of the two points. -/
def swapE : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

variable (α : Ordinal.{u})

/-- **The context**: `TieInstance.ctx` (the scheme `SeparationObstruction.S` labelled `⊤` at `r`)
with its two points exchanged: the free cell `y` lies on the point `1`, off the root, and the dead
cell `e` on the root point `0`. -/
noncomputable def ctxP : StageType.{u} α 2 := (ctx α).reindex swapE

/-- **The donor**: `TieInstance.don` (the same scheme labelled `⊥`) with its points exchanged. -/
noncomputable def donP : StageType.{u} α 2 := (don α).reindex swapE

theorem restrictFace_ctx_swap : restrictFace swapE.toEmbedding (ctx α) = some (ctxP α) :=
  StageType.restrictFace_equiv (ctx α) swapE

theorem restrictFace_don_swap : restrictFace swapE.toEmbedding (don α) = some (donP α) :=
  StageType.restrictFace_equiv (don α) swapE

/-- The embedding of the point `0` as the point `1`. -/
def e1 : Fin 1 ↪ Fin 2 := Fin.castSuccEmb.trans swapE.toEmbedding

theorem map_e1_mem_faces : univ.map e1 ∈ (ctx α).toCellScheme.faces := by
  change univ.map e1 ∈ cells.faces
  decide

/-- The root face: the dead cell on one point. -/
noncomputable def pt1 : StageType.{u} α 1 := (ctx α).comap e1 (map_e1_mem_faces α)

theorem restrictFace_ctxP : restrictFace Fin.castSuccEmb (ctxP α) = some (pt1 α) :=
  (StageType.restrictFace_reindex (ctx α) Fin.castSuccEmb swapE).trans
    (restrictFace_of_mem _ _ _)

theorem restrictFace_ctxP_root :
    restrictFace ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb) (ctxP α) =
      some (pt1 α) := by
  rw [refl_trans_castSuccEmb]; exact restrictFace_ctxP α

theorem isLegal_ctxP : (ctxP α).IsLegal :=
  StageType.IsLegal.reindex (t := ctx α) SeparationObstruction.isLegal_S swapE

theorem donP_mem_cofaces : donP α ∈ (pt1 α).cofaces := by
  refine ⟨StageType.IsLegal.reindex (t := don α) SeparationObstruction.isLegal_S swapE, ?_⟩
  rw [← restrictFace_ctxP α]
  refine (StageType.restrictFace_reindex (don α) Fin.castSuccEmb swapE).trans
    (Eq.trans ?_ (StageType.restrictFace_reindex (ctx α) Fin.castSuccEmb swapE).symm)
  refine restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  have hvis : ∀ i : Fin 5, i ∈ S.{u}.visibleCells e1 → i ≠ 4 := by decide
  have h4 := hvis i hi
  fin_cases i <;> first | exact absurd rfl h4 | rfl

/-! ### The cells after the exchange -/

theorem mem_visibleCells_swap (c : Fin 5) : c ∈ S.{u}.visibleCells swapE.toEmbedding := by
  revert c; decide

/-- The cell of the context over the cell `c` of `S`. -/
noncomputable def cellC (c : Fin 5) : Fin (ctxP α).card :=
  (StageType.exists_faceCell_eq (restrictFace_ctx_swap α) (mem_visibleCells_swap c)).choose

theorem faceCell_cellC (c : Fin 5) :
    (ctx α).faceCell (restrictFace_ctx_swap α) (cellC α c) = c :=
  (StageType.exists_faceCell_eq (restrictFace_ctx_swap α) (mem_visibleCells_swap c)).choose_spec

/-- The cell of the donor over the cell `c` of `S`. -/
noncomputable def cellD (c : Fin 5) : Fin (donP α).card :=
  (StageType.exists_faceCell_eq (restrictFace_don_swap α) (mem_visibleCells_swap c)).choose

theorem faceCell_cellD (c : Fin 5) :
    (don α).faceCell (restrictFace_don_swap α) (cellD α c) = c :=
  (StageType.exists_faceCell_eq (restrictFace_don_swap α) (mem_visibleCells_swap c)).choose_spec

theorem grade_cellC (c : Fin 5) : (ctxP α).toCellScheme.grade (cellC α c) = cells.grade c := by
  rw [← StageType.grade_faceCell (restrictFace_ctx_swap α), faceCell_cellC]; rfl

theorem grade_cellD (c : Fin 5) : (donP α).toCellScheme.grade (cellD α c) = cells.grade c := by
  rw [← StageType.grade_faceCell (restrictFace_don_swap α), faceCell_cellD]; rfl

/-- A labelling `lab v w s` is `⊥` at the cells of scope inside `{1}`. -/
theorem lab_eq_bot_of_scope {v w s : Label.{u}} {c : Fin 5} (hc : cells.scope c ⊆ {1}) :
    lab v w s c = ⊥ := by
  have key : ∀ c : Fin 5, cells.scope c ⊆ {1} → c = 1 := by decide
  rw [key c hc]; rfl

/-- The root cells lie over cells of `S` of scope inside `{1}`. -/
theorem scope_root {D t : StageType.{u} α 2} (hD : restrictFace swapE.toEmbedding D = some t)
    {f : Fin 1 ↪ Fin 2} (hf : ∀ z, f z = 0) {q : StageType.{u} α 1} (hq : restrictFace f t = some q)
    (i : Fin q.card) :
    D.toCellScheme.scope (D.faceCell hD (t.faceCell hq i)) ⊆ {1} := by
  rw [StageType.scope_faceCell, StageType.scope_faceCell]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  obtain ⟨z, -, rfl⟩ := mem_map.mp hy
  rw [hf]
  decide

/-! ### The requests -/

/-- **The bottom requests** with the cap and the marker at the cell `r`. -/
noncomputable def reqP : GrowthRequests (ctxP α) (donP α).toScheme where
  cap := cellC α 4
  marker := cellC α 4
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := cellC α 4
  offset _ := 0

theorem label_ctxP (c : Fin 5) : (ctxP α).label (cellC α c) = lab ⊥ ⊥ ⊤ c := by
  rw [← StageType.label_faceCell (restrictFace_ctx_swap α), faceCell_cellC]; rfl

theorem label_donP (y : Fin (donP α).card) : (donP α).label y = ⊥ := by
  rw [← StageType.label_faceCell (restrictFace_don_swap α)]
  have key : ∀ c : Fin 5, lab ⊥ ⊥ ⊥ c = (⊥ : Label.{u}) := by intro c; fin_cases c <;> rfl
  exact key _

theorem threshold_reqP : (reqP α).threshold = 2 := grade_cellC α 4

theorem scope_cellC_four : (ctxP α).toCellScheme.scope (cellC α 4) = univ := by
  have h := StageType.scope_faceCell (restrictFace_ctx_swap α) (cellC α 4)
  rw [faceCell_cellC] at h
  have hu : cells.scope 4 = univ := by decide
  change cells.scope 4 = _ at h
  rw [hu] at h
  exact eq_univ_of_card _ (by rw [← card_map swapE.toEmbedding, ← h, card_univ])

theorem correctAt_reqP (j : Fin (donP α).card) :
    (reqP α).CorrectAt (ctxP α).label j ((donP α).label j) := by
  rw [label_donP]
  exact ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_reqP : (reqP α).ClassCalibrated (restrictFace_ctxP_root α) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := scope_cellC_four α
  label_cap := by
    rw [show (reqP α).cap = cellC α 4 from rfl, label_ctxP]; exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨le_rfl, Nat.zero_le _, by
    rw [show (reqP α).marker = cellC α 4 from rfl, label_ctxP]; exact top_ne_bot⟩
  root _ := ((ctxP α).grade_le _).trans_eq (threshold_reqP α).symm
  arity := (threshold_reqP α).ge

theorem label_root (i : Fin (pt1 α).card) :
    (ctxP α).label ((ctxP α).faceCell (restrictFace_ctxP_root α) i) = ⊥ := by
  rw [← StageType.label_faceCell (restrictFace_ctx_swap α)]
  exact lab_eq_bot_of_scope (scope_root α (restrictFace_ctx_swap α) (fun z ↦ by fin_cases z; rfl)
    _ i)

theorem hasRelativeLiftOnClass_reqP :
    (reqP α).HasRelativeLiftOnClass (restrictFace_ctxP_root α) (donP_mem_cofaces α).2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_reqP α)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root α) (donP_mem_cofaces α).1 Nat.one_pos

/-! ### The ambient state and the prescription -/

/-- The value `ω + 1`, the pinned value: finite part `1`, not self-visible at `2`. -/
noncomputable abbrev valY : Label.{u} := gridPoint 1 1

/-- The value `ω + 2`. -/
noncomputable abbrev valZ : Label.{u} := gridPoint 2 1

/-- The ambient on the context: `ω + 1` at `y` and `z`, `⊥` elsewhere. -/
noncomputable def ambCtx (x : Fin (ctxP α).card) : Label.{u} :=
  lab valY ⊥ ⊥ ((ctx α).faceCell (restrictFace_ctx_swap α) x)

/-- The prescription on the context: `ω · 2 + 1` at `y` and `z`, `⊥` elsewhere. -/
noncomputable def preCtx (x : Fin (ctxP α).card) : Label.{u} :=
  lab (gridPoint 1 2) ⊥ ⊥ ((ctx α).faceCell (restrictFace_ctx_swap α) x)

/-- The ambient on the donor: `ω + 2` at `y`, `z`, `o`, `r`. -/
noncomputable def ambDon (y : Fin (donP α).card) : Label.{u} :=
  lab valZ valZ valZ ((don α).faceCell (restrictFace_don_swap α) y)

/-- The prescription on the donor: `ω + 2` at `y`, `z`, `o` and `ω · 2 + 2` at `r`. -/
noncomputable def preDon (y : Fin (donP α).card) : Label.{u} :=
  lab valZ valZ (gridPoint 2 2) ((don α).faceCell (restrictFace_don_swap α) y)

theorem isLawful_ambCtx : (ctxP α).rows.IsLawful (ambCtx α) :=
  GrowthRequests.isLawful_root (restrictFace_ctx_swap α)
    (isLawful_lab (isSelfVisible_gridPoint 1 1) (isSelfVisible_bot 2) (isSelfVisible_bot 2)
      bot_le rfl)

theorem isLawful_preCtx : (ctxP α).rows.IsLawful (preCtx α) :=
  GrowthRequests.isLawful_root (restrictFace_ctx_swap α)
    (isLawful_lab (isSelfVisible_gridPoint 1 2) (isSelfVisible_bot 2) (isSelfVisible_bot 2)
      bot_le rfl)

theorem isLawful_ambDon : (donP α).rows.IsLawful (ambDon α) :=
  GrowthRequests.isLawful_root (restrictFace_don_swap α)
    (isLawful_lab ((isSelfVisible_gridPoint 2 1).mono (by omega)) (isSelfVisible_gridPoint 2 1)
      (isSelfVisible_gridPoint 2 1) le_rfl rfl)

theorem isLawful_preDon : (donP α).rows.IsLawful (preDon α) :=
  GrowthRequests.isLawful_root (restrictFace_don_swap α)
    (isLawful_lab ((isSelfVisible_gridPoint 2 1).mono (by omega)) (isSelfVisible_gridPoint 2 1)
      (isSelfVisible_gridPoint 2 2) le_rfl rfl)

theorem hf0_root : ∀ z, ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb) z = 0 := by
  intro z; fin_cases z; rfl

theorem hf0_castSucc : ∀ z, (Fin.castSuccEmb : Fin 1 ↪ Fin 2) z = 0 := by
  intro z; fin_cases z; rfl

theorem root_amb (i : Fin (pt1 α).card) :
    ambDon α ((donP α).faceCell (donP_mem_cofaces α).2 i) =
      ambCtx α ((ctxP α).faceCell (restrictFace_ctxP_root α) i) := by
  exact (lab_eq_bot_of_scope (scope_root α (restrictFace_don_swap α) hf0_castSucc
    (donP_mem_cofaces α).2 i)).trans (lab_eq_bot_of_scope (scope_root α (restrictFace_ctx_swap α)
      hf0_root (restrictFace_ctxP_root α) i)).symm

theorem root_pre (i : Fin (pt1 α).card) :
    preDon α ((donP α).faceCell (donP_mem_cofaces α).2 i) =
      preCtx α ((ctxP α).faceCell (restrictFace_ctxP_root α) i) := by
  exact (lab_eq_bot_of_scope (scope_root α (restrictFace_don_swap α) hf0_castSucc
    (donP_mem_cofaces α).2 i)).trans (lab_eq_bot_of_scope (scope_root α (restrictFace_ctx_swap α)
      hf0_root (restrictFace_ctxP_root α) i)).symm

theorem lab_mem {Γ : Finset Label.{u}} {v w s : Label.{u}} (hv : v ∈ Γ) (hw : w ∈ Γ) (hs : s ∈ Γ)
    (h0 : ⊥ ∈ Γ) (c : Fin 5) : lab v w s c ∈ Γ := by
  fin_cases c <;> assumption

/-- The capped agreement of two labellings `lab v ⊥ ⊥`-style at a cap below their positive
values. -/
theorem min_lab_eq {v w s v' w' s' c : Label.{u}} (hv : min v c = min v' c)
    (hw : min w c = min w' c) (hs : min s c = min s' c) (x : Fin 5) :
    min (lab v w s x) c = min (lab v' w' s' x) c := by
  fin_cases x <;> first | exact hv | exact hw | exact hs | rfl

/-! ### The pin -/

/-- **The pin at a cap above the finite parts of the values**: for any finite set `Γ`, every
height at `2` (`Scheme.heightSet Γ B' 2`) at least the cap `gridPoint (N) 0 = N`,
`N = Γ.sup labelFinNat + 3`, lies above `ω + 1`: the grid points at least `N` are in the blocks
from `1` on, above `ω + 1`; a value of `Γ` at least `N` is not finite (its finite part is below
`N`), and a value of the block `ω` self-visible at `2` is at least `ω + 2`. -/
theorem pin_heightSet (Γ : Finset Label.{u}) (B' : ℕ) :
    ∀ x ∈ Scheme.heightSet Γ B' 2, gridPoint (Γ.sup labelFinNat + 3) 0 ≤ x → valY < x := by
  intro x hx hcx
  set N := Γ.sup labelFinNat + 3 with hN
  rcases Scheme.mem_heightSet.mp hx with hg | ⟨hxΓ, hxv⟩
  · rcases mem_grid.mp hg with rfl | ⟨b, -, rfl⟩
    · exact absurd (le_bot_iff.mp hcx) (gridPoint_ne_bot _ _)
    · rw [gridPoint_le_gridPoint_iff_lex] at hcx
      rw [valY, gridPoint_lt_gridPoint_iff_lex]
      omega
  · induction x using recBotCoeTop with
    | bot => exact absurd (le_bot_iff.mp hcx) (gridPoint_ne_bot _ _)
    | top => exact lt_of_le_of_ne le_top (gridPoint_ne_top 1 1)
    | coe o =>
      have hfin : finNat o ≤ Γ.sup labelFinNat := Finset.le_sup (f := labelFinNat) hxΓ
      rw [isSelfVisible_coe, finNat_spec] at hxv
      have hv2 : 2 ≤ finNat o := by exact_mod_cast hxv
      rw [gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe, Nat.cast_zero, mul_zero,
        zero_add] at hcx
      rw [valY, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, Nat.cast_one, mul_one]
      by_contra hle
      push Not at hle
      rcases lt_or_ge o Ordinal.omega0 with hω | hω
      · obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hω
        have hk : finNat (k : Ordinal.{u}) = k := by
          simpa using finNat_add_natCast (l := (0 : Ordinal.{u})) Order.isSuccPrelimit_bot k
        have hNk : N ≤ k := by exact_mod_cast hcx
        omega
      · have hr := Ordinal.add_sub_cancel_of_le hω
        set r := o - Ordinal.omega0 with hrdef
        have hr1 : r ≤ 1 := by
          rw [← hr] at hle
          exact (add_le_add_iff_left Ordinal.omega0).mp hle
        obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (hr1.trans_lt Ordinal.one_lt_omega0)
        rw [hk] at hr hr1
        have hk1 : k ≤ 1 := by exact_mod_cast hr1
        have hfk : finNat o = k := by
          rw [← hr]; exact finNat_add_natCast Ordinal.isSuccLimit_omega0.isSuccPrelimit k
        omega

end PinInstance

namespace StageType

open PinInstance SeparationObstruction

/-- **The extension over the tower at a positive cap at the seed position fails at the choice of
the assembly, for the repaired scheme** (agreement heights in `Scheme.heightSet`), by a pin
(`Seed.not_towerExtensionPos_of_glued_pin`): at the stage `ω`, the seed of
`StageType.exists_growthSeed_of_isSuccLimit` over the context `PinInstance.ctxP` (the legal scheme
`SeparationObstruction.S` with its points exchanged, labelled `⊤` at `r`), the root `{0}` (the
dead cell), the donor `PinInstance.donP` (the same scheme labelled `⊥`) and the bottom requests
`PinInstance.reqP`; the ambient state is `ω + 1` at the context's cells `y`, `z` and `ω + 2` at the
donor's cells `y`, `z`, `o`, `r`; the prescription is `ω · 2 + 1` at the context's `y`, `z`, and
`ω + 2`, `ω + 2`, `ω + 2`, `ω · 2 + 2` at the donor's; the cap is `N = sup (finite parts of the
values of the choice) + 3`, a natural number above every finite value of the choice.  The context
cell `y` (grade `1`, ambient `ω + 1`, not a height) is pinned: every height at least `N` lies above
`ω + 1` (`PinInstance.pin_heightSet`). -/
theorem not_towerExtensionPosAtSeed_seedChoice :
    ¬ TowerExtensionPosAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := by
  intro h
  have hα : Order.IsSuccLimit (ω : Ordinal.{u}) := Ordinal.isSuccLimit_omega0
  have hp : restrictFace (Function.Embedding.refl (Fin 1)) (pt1 ω) = some (pt1 ω) :=
    (restrictFace_trans (ctxP ω) _ _ (restrictFace_ctxP ω)).trans (restrictFace_ctxP_root ω)
  obtain ⟨I, hI, hdA⟩ := exists_growthSeed_of_isSuccLimit hα (t' := ctxP ω) (isLegal_ctxP ω)
    (restrictFace_ctxP ω) hp (donP_mem_cofaces ω)
  have key := towerExtensionPos_of_atSeed h hα I (Function.Embedding.refl (Fin 1)) hI
    (restrictFace_ctxP ω) (restrictFace_ctxP_root ω) (donP_mem_cofaces ω) hdA Nat.one_pos
    (reqP ω) (correctAt_reqP ω) (classCalibrated_reqP ω) (hasRelativeLiftOnClass_reqP ω) 2 le_rfl
    le_rfl
  set g := Function.Embedding.refl (Fin 1) with hg
  set N := (I.seedValues g).sup labelFinNat + 3 with hN
  have hC : 1 ≤ (I.attachment g).card := by
    have h0 : 0 < I.left.card := hI ▸ Fin.pos (cellC ω 0)
    exact Fin.pos (I.attachCtxCell g ⟨0, h0⟩)
  have hY : valY ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 1) (f := 1) hC (by omega))
  have hZ : valZ ∈ I.seedValues g :=
    I.codeSet_subset_seedValues g (mem_codeSet (i := 1) (f := 2) hC (by omega))
  have h0Γ := I.bot_mem_seedValues g
  have hcY : gridPoint N 0 ≤ valY := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hcZ : gridPoint N 0 ≤ valZ := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hc12 : gridPoint N 0 ≤ gridPoint 1 2 := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  have hc22 : gridPoint N 0 ≤ gridPoint 2 2 := gridPoint_le_gridPoint_iff_lex.mpr (.inl (by omega))
  refine Seed.not_towerExtensionPos_of_glued_pin (I.seedHeight_pos g) (I.card_le_seedHeight g)
    (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx) hI (restrictFace_ctxP_root ω)
    (donP_mem_cofaces ω).2 hdA (classCalibrated_reqP ω) le_rfl le_rfl le_rfl
    (isLawful_ambCtx ω) (isLawful_preCtx ω) (isLawful_ambDon ω) (isLawful_preDon ω)
    (root_amb ω) (root_pre ω) (fun x ↦ lab_mem hY h0Γ h0Γ h0Γ _)
    (fun y ↦ lab_mem hZ hZ hZ h0Γ _) (x₀ := cellC ω 0)
    (GrowthRequests.mem_below_cap (reqP ω) (classCalibrated_reqP ω).scope_cap
      (((ctxP ω).grade_le _).trans_eq (threshold_reqP ω).symm))
    (by rw [label_ctxP]; rfl) (by rw [ambCtx, faceCell_cellC]; exact gridPoint_ne_bot 1 1)
    (by rw [preCtx, faceCell_cellC]; exact gridPoint_ne_bot 1 2) (c := gridPoint N 0)
    ((isSelfVisible_gridPoint N 0).mono (by omega)) (gridPoint_ne_bot N 0)
    (fun x ↦ min_lab_eq (by rw [min_eq_right hc12, min_eq_right hcY]) rfl rfl _)
    (fun y ↦ min_lab_eq rfl rfl (by rw [min_eq_right hc22, min_eq_right hcZ]) _)
    (xa := cellC ω 0) (y₁ := cellD ω 0) (y₃ := cellD ω 4) ((grade_cellC ω 0).trans_le (by decide))
    ((grade_cellD ω 0).trans_le (by decide)) (grade_cellD ω 4) ?_ ?_ ?_ ?_ ?_ key
  · rw [ambCtx, ambDon, faceCell_cellC, faceCell_cellD]
    exact gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)
  · intro x hx hcx
    rw [ambCtx, faceCell_cellC]
    exact pin_heightSet _ _ x hx hcx
  · rw [preCtx, preDon, faceCell_cellC, faceCell_cellD]
    exact gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)
  · rw [preCtx, preDon, faceCell_cellC, faceCell_cellD]
    exact gridPoint_lt_gridPoint_iff_lex.mpr (.inl (by omega))
  · rw [preDon, faceCell_cellD]
    exact fun h' ↦ absurd (gridPoint_le_gridPoint_iff_lex.mp h') (by omega)

/-- The extension over the tower gives its case at a positive cap. -/
theorem towerExtensionPosAtSeed_of_towerExtensionAtSeed
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    (h : TowerExtensionAtSeed.{u} H Γ B') : TowerExtensionPosAtSeed.{u} H Γ B' :=
  fun _ _ _ I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm c hc _ q hq P hP hPA hPq _ ↦
    h I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm c hc q hq P hP hPA hPq

/-- **The extension over the tower at the seed position fails at the choice of the assembly, for
the repaired scheme** (`StageType.not_towerExtensionPosAtSeed_seedChoice`). -/
theorem not_towerExtensionAtSeed_seedChoice :
    ¬ TowerExtensionAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := fun h ↦
  not_towerExtensionPosAtSeed_seedChoice (towerExtensionPosAtSeed_of_towerExtensionAtSeed h)

end StageType

end VaughtConjecture

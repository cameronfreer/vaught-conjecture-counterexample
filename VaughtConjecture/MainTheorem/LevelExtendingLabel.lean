/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLabel
import VaughtConjecture.MainTheorem.ReplicatedLevelMirror
import VaughtConjecture.MainTheorem.ReplicatedLevelQuad

/-!
# A lawful labelling of a re-rendered level extending the labels of the attachment

Roadmap, Layer 3 ((R3) and (R4), the labelling input of the levels re-rendered per grade).

**The statement** (`Seed.ALvl.HasExtendingLabel`, `Seed.HasExtendingLabelLevel`,
`Seed.ALvl.Good.HasExtendingLabelRep`): a lawful section of the scheme of a level (or of the level
with its copies at the mixed faces) that is the labelling of the attachment on its cells, literally:
`⊤`, `⊥` and ordinal labels of any size included.  It is the analogue at a level of
`Seed.HasExtendingLabel`.

**The construction** (`Seed.ALvl.extLabel`): compress, render, expand.
* The **compressed labelling** of the attachment (`Seed.compressedLabel`, the block compression of
  its labels at the grade `m + 2`) is lawful on the attachment and admitted at every grade
  (`Seed.attachAdmits_compressedLabel`); its values are self-visible at `1`.  It is a state lawful
  below every pair, but in general neither in the code grid of the level nor canonical: a level
  renders every lawful admitted state through its own orbit code, so neither is asked.
* **Rendering**: the section of a good level at a state lawful on the attachment, self-visible at
  `1` and admitted at the grade of the level is a lawful section of the whole scheme of the level
  (`Seed.ALvl.Good.isLawful_σ`): below `(univ, j)` it is lawful (`Seed.ALvl.Good.lawful`); a cell
  above `(univ, j)` has a scope other than the ground set, and below such a cell the level is the
  attachment, read literally (`Seed.ALvl.Good.literal`).
* **Expansion**: the block expansion (`Label.blockExpand`) is a witness at every grade sending only
  `⊥` to `⊥`, so it keeps the rendered section lawful, and it inverts the compression on the labels
  of the attachment (`Seed.blockExpand_compressedLabel`).

**Result** (`Seed.ALvl.Good.hasExtendingLabel`, `Seed.hasExtendingLabelLevel`,
`Seed.ALvl.Good.hasExtendingLabelRep`): every good level whose admission predicate admits the
compressed labelling has a lawful labelling extending the labels of the attachment, and so has the
level with its copies (a copy carries the label of its original).  For the levels over requests
calibrated on the class with the labels pair correct, this holds at every grade `j + 1 ≤ m + 2`,
for every height `H > 0` bounding the cells of the attachment and every block bound `B` with
`2 · #cells ≤ B`, both fixed by the seed: no bound depending on the labels and no set of values is
asked (`Seed.hasExtendingLabel_attachAdmits` asks a set of values containing the compressed labels
and a grid point above them).

**The bottom state.**  The labelling uses only the literal reading of the attachment and the
lawfulness of the section: the literal reading holds at every state lawful below `(univ, 1)`, and
the lawfulness of the section at every lawful admitted state with values self-visible at `1`.  The
compressed labelling is such a state (`Seed.attachAdmits_compressedLabel`), and it is the bottom
state when every label is `⊥`.  The ladder recovery (`Seed.lvLevel_σ_embed`, which asks a value
other than `⊥`) is not used.
* When some label of the attachment is not `⊥`, the labelling reads the ladder base as the
  expansion of the first level at the compressed labelling (`Seed.lvLevel_extLabel_embed`).
* When every label of the attachment is `⊥` (the bottom state), the compressed labelling is the
  bottom state and the labelling reads the ladder base of the levels above the first as `⊥` where
  the first level is `⊥` and as `⊤` elsewhere (`Seed.lvLevel_extLabel_embed_bot`: the gap value
  `ω * B + (j + 3)` lies in no block of the labels, so it expands to `⊤`).  The constant labelling
  `⊥` extends the labels as well (`Seed.ALvl.hasExtendingLabel_of_forall_eq_bot`).
* A cell of the attachment labelled `⊥` is labelled `⊥` (compression and expansion fix `⊥`).

**The test inputs** (`TieInstance.hasExtendingLabelLevel_tie`,
`ApexInstance.hasExtendingLabelLevel_apex`, `QuadInstance.hasExtendingLabelLevel_quad`): at every
seed of each input, every level up to the grade `m + 2` has the extending labelling, and it reads
`⊤` at the cell of the attachment at a context cell labelled `⊤` (`cellR ω`, the apex of
`topType α`, the apex of `quadType hα`).

## References

Lawful sections are [Kni26, Definition 2.5.4]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType AvailableTopDeterminationCounterexample
open scoped Ordinal

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **Lawfulness from lawfulness below the graded index of every cell.** -/
theorem isLawful_of_forall_isLawfulBelow_gradedIndex {w : ι → Label.{u}}
    (h : ∀ z, R.IsLawfulBelow (D.gradedIndex z) fun d ↦ w d) : R.IsLawful w where
  orderly z := (isLawfulBelow_iff_forall.mp (h z)).1 z (D.mem_below_gradedIndex z)
  locality s := (isLawfulBelow_iff_forall.mp (h s)).2.1 s (D.mem_below_gradedIndex s)
  availability s t hst hg :=
    (isLawfulBelow_iff_forall.mp (h t)).2.2 s t (D.mem_below_gradedIndex t) hst hg

end CellScheme.Rows

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-! ### The statement -/

/-- **A lawful labelling of a level extending the labels of the attachment**: a lawful section of
the scheme of the level that is the labelling of the attachment on its cells. -/
def ALvl.HasExtendingLabel {j : ℕ} (N : I.ALvl g H j) : Prop :=
  ∃ q : Fin N.S.card → Label.{u}, N.S.rows.IsLawful q ∧
    ∀ c, q (N.attEmb c) = (I.attachmentType g).label c

variable (I g H B) in
/-- **The extending labelling at the level of the grade `j + 1`.** -/
def HasExtendingLabelLevel {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) (j : ℕ) : Prop :=
  (I.lvLevel g H B hd Q j).HasExtendingLabel

/-- **A lawful labelling of a level with its copies extending the labels of the attachment**: a
lawful section of the level mirrored at the mixed faces that is the labelling of the attachment on
its cells (the cells of the level come first). -/
def ALvl.Good.HasExtendingLabelRep {j : ℕ} {N : I.ALvl g H j}
    {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} (hN : N.Good B A) : Prop :=
  ∃ q : Fin (N.S.card + N.S.copyCount (I.mixedFaces g)) → Label.{u}, hN.rep.rows.IsLawful q ∧
    ∀ c, q (Fin.castAdd _ (N.attEmb c)) = (I.attachmentType g).label c

/-! ### Rendering: the section of a good level is lawful on the whole scheme -/

namespace ALvl.Good

variable {j : ℕ} {N : I.ALvl g H j} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}

/-- Lawfulness below a pair off the full face is lawfulness on the attachment, for a good level
at any admission predicate. -/
theorem isLawfulBelow_attEmb_iff (hN : N.Good B A) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {w : Fin N.S.card → Label.{u}} :
    N.S.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      (I.attachment g).rows.IsLawfulBelow X (fun e ↦ w (N.attEmb e)) := by
  have h : (I.attachment g).toCellScheme.IsSourcePrefix N.S.toCellScheme N.attEmb X :=
    ⟨hN.lowerEmb, hN.scope_attEmb, fun z hz ↦ hN.mem_range z fun he ↦
      hX (univ_subset_iff.mp (he ▸ hz.1))⟩
  rw [← h.isLawfulBelow_iff le_rfl, hN.comap_rows]
  rfl

/-- **The section of a good level is a lawful section of the whole scheme** at a state lawful on
the attachment, self-visible at `1` and admitted at the grade of the level: below `(univ, j)` it is
lawful; every other cell is a cell of the attachment, of scope other than the ground set, and below
it the level is the attachment read literally. -/
theorem isLawful_σ (hN : N.Good B A) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : (I.attachment g).rows.IsLawful P) (hv : ∀ e, IsSelfVisible 1 (P e)) (hA : A j P) :
    N.S.rows.IsLawful (N.σ P) := by
  have hlow := hN.lawful P (hP.isLawfulBelow _) hv hA
  have hP1 := hP.isLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
  refine Rows.isLawful_of_forall_isLawfulBelow_gradedIndex fun z ↦ ?_
  by_cases hz : N.S.toCellScheme.grade z ≤ j
  · have hle : N.S.toCellScheme.gradedIndex z ≤ ((univ : Finset (Fin (m + 2))), j) :=
      ⟨subset_univ _, hz⟩
    exact hlow.mono hle
  · have hX : (N.S.toCellScheme.gradedIndex z).1 ≠ univ := (N.inv z).resolve_left hz
    refine (hN.isLawfulBelow_attEmb_iff hX).mpr ?_
    exact (Rows.isLawfulBelow_congr (w' := fun e ↦ N.σ P (N.attEmb e))
      fun e _ ↦ (hN.literal P hP1 e).symm).mp (hP.isLawfulBelow _)

end ALvl.Good

/-! ### Expansion: the extending labelling -/

namespace ALvl

variable {j : ℕ}

variable (N : I.ALvl g H j) in
/-- **The extending labelling of a level**: the block expansion of the section of the level at
the compressed labelling of the attachment. -/
noncomputable def extLabel (z : Fin N.S.card) : Label.{u} :=
  blockExpand (I.attachLabels g) (N.σ (I.compressedLabel g) z)

variable {N : I.ALvl g H j} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}

/-- **The extending labelling is lawful** on a good level whose admission predicate admits the
compressed labelling at the grade of the level. -/
theorem Good.isLawful_extLabel (hN : N.Good B A) (hA : A j (I.compressedLabel g)) :
    N.S.rows.IsLawful N.extLabel :=
  (hN.isLawful_σ isLawful_compressedLabel
    ((I.attachmentBase g).isSelfVisible_one_of_isLawful isLawful_compressedLabel)
    hA).map_of_apply_eq_bot (K := univ.sup N.S.toCellScheme.grade)
    (fun z ↦ le_sup (f := N.S.toCellScheme.grade) (mem_univ z)) (isWitness_blockExpand _)
    fun _ h ↦ blockExpand_eq_bot_iff.mp h

/-- **The extending labelling is the labelling of the attachment on its cells**, literally: `⊤`,
`⊥` and ordinal labels of any size included. -/
theorem Good.extLabel_attEmb (hN : N.Good B A) (c : Fin (I.attachment g).card) :
    N.extLabel (N.attEmb c) = (I.attachmentType g).label c := by
  rw [extLabel, hN.literal _ (isLawful_compressedLabel.isLawfulBelow _) c]
  exact blockExpand_compressedLabel c

/-- **A good level admitting the compressed labelling has a lawful labelling extending the labels
of the attachment.** -/
theorem Good.hasExtendingLabel (hN : N.Good B A) (hA : A j (I.compressedLabel g)) :
    N.HasExtendingLabel :=
  ⟨N.extLabel, hN.isLawful_extLabel hA, hN.extLabel_attEmb⟩

/-- **The extending labelling passes to the copies**: a copy carries the label of its original. -/
theorem Good.hasExtendingLabelRep_of (hN : N.Good B A) (h : N.HasExtendingLabel) :
    hN.HasExtendingLabelRep := by
  obtain ⟨q, hq, hqc⟩ := h
  exact ⟨fun t ↦ q (N.S.mirrorOrig (I.mixedFaces g) t),
    (Scheme.mirrorData hN.not_subset_scope).isLawful_comp hq (Scheme.saturated_mirrorData _),
    fun c ↦ by simp only [Scheme.mirrorOrig_castAdd]; exact hqc c⟩

/-- **The level with its copies has a lawful labelling extending the labels of the attachment.** -/
theorem Good.hasExtendingLabelRep (hN : N.Good B A) (hA : A j (I.compressedLabel g)) :
    hN.HasExtendingLabelRep :=
  hN.hasExtendingLabelRep_of (hN.hasExtendingLabel hA)

/-- **The bottom labels**: when every label of the attachment is `⊥`, the constant labelling `⊥`
extends them, at every level. -/
theorem hasExtendingLabel_of_forall_eq_bot (N : I.ALvl g H j)
    (h : ∀ c, (I.attachmentType g).label c = ⊥) : N.HasExtendingLabel :=
  ⟨fun _ ↦ ⊥, Rows.isLawful_const_bot, fun c ↦ (h c).symm⟩

end ALvl

/-! ### The levels -/

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **Every level has a lawful labelling extending the labels of the attachment**, for requests
calibrated on the class with the labels pair correct, every height `H > 0` bounding the cells of
the attachment and every block bound `B` with `2 · #cells ≤ B`, at every grade `j + 1 ≤ m + 2`. -/
theorem hasExtendingLabelLevel (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hB : 2 * (I.attachment g).card ≤ B) (j : ℕ) (hj : j + 1 ≤ m + 2) :
    I.HasExtendingLabelLevel g H B hd Q j :=
  (lvLevel_good hH hcard hQ hB j hj).hasExtendingLabel
    (attachAdmits_compressedLabel hd hpair hQ (j + 1))

/-- **Every level with its copies has a lawful labelling extending the labels of the attachment**,
under the hypotheses of `Seed.hasExtendingLabelLevel`. -/
theorem hasExtendingLabelLevel_rep (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hB : 2 * (I.attachment g).card ≤ B) (j : ℕ) (hj : j + 1 ≤ m + 2) :
    (lvLevel_good (B := B) (hd := hd) hH hcard hQ hB j hj).HasExtendingLabelRep :=
  (lvLevel_good hH hcard hQ hB j hj).hasExtendingLabelRep
    (attachAdmits_compressedLabel hd hpair hQ (j + 1))

/-! ### The ladder base under the extending labelling, and the bottom state -/

/-- **With some label other than `⊥`, the extending labelling reads the ladder base as the
expansion of the first level at the compressed labelling** (the ladder recovery,
`Seed.lvLevel_σ_embed`). -/
theorem lvLevel_extLabel_embed (hcard : (I.attachmentBase g).S.card ≤ H)
    (hpos : ∃ c, (I.attachmentType g).label c ≠ ⊥) (j : ℕ) (t : Fin (I.lvBase g H).card) :
    (I.lvLevel g H B hd Q j).extLabel ((I.lvLevel g H B hd Q j).embed t) =
      blockExpand (I.attachLabels g) (I.lvBaseSec g H (I.compressedLabel g) t) := by
  obtain ⟨c, hc⟩ := hpos
  rw [ALvl.extLabel, lvLevel_σ_embed hcard j _ (isLawful_compressedLabel.isLawfulBelow _)
    ((I.attachmentBase g).isSelfVisible_one_of_isLawful isLawful_compressedLabel)
    ⟨c, fun h ↦ hc ((blockCompress_eq_bot_iff (label_mem_attachLabels c) _).mp h)⟩]

/-- With every label `⊥`, the compressed labelling is the bottom state. -/
theorem compressedLabel_eq_bot (h : ∀ c, (I.attachmentType g).label c = ⊥) :
    I.compressedLabel g = fun _ ↦ ⊥ :=
  funext fun c ↦ (blockCompress_eq_bot_iff (label_mem_attachLabels c) _).mpr (h c)

/-- With every label `⊥`, the labels occupy no block. -/
theorem blockCount_attachLabels_eq_zero (h : ∀ c, (I.attachmentType g).label c = ⊥) :
    blockCount (I.attachLabels g) = 0 := by
  rw [blockCount, Finset.card_eq_zero, blockSet, eq_empty_iff_forall_notMem]
  intro μ hμ
  obtain ⟨x, hx, hμx⟩ := mem_biUnion.mp hμ
  obtain ⟨c, -, rfl⟩ := mem_image.mp hx
  rw [h c] at hμx
  exact notMem_empty μ hμx

/-- **The bottom state**: when every label of the attachment is `⊥`, the extending labelling reads
the ladder base of the level at the grade `j + 2` as `⊥` where the first level is `⊥` and as `⊤`
elsewhere: the gap value `ω * B + (j + 3)` (`Seed.lvLevel_σ_embed_bot`) lies in no block of the
labels.  The labelling stays lawful (`Seed.hasExtendingLabelLevel`); only the ladder recovery
fails there. -/
theorem lvLevel_extLabel_embed_bot (h : ∀ c, (I.attachmentType g).label c = ⊥) (j : ℕ)
    (t : Fin (I.lvBase g H).card) :
    (I.lvLevel g H B hd Q (j + 1)).extLabel ((I.lvLevel g H B hd Q (j + 1)).embed t) =
      if I.lvBaseSec g H (fun _ ↦ ⊥) t = ⊥ then ⊥ else ⊤ := by
  rw [ALvl.extLabel, compressedLabel_eq_bot h, lvLevel_σ_embed_bot j t]
  split_ifs
  · rfl
  · rw [gridPoint, blockExpand_coe, expandOrd_of_not]
    rintro ⟨i, hi, -⟩
    rw [blockCount_attachLabels_eq_zero h] at hi
    exact Nat.not_lt_zero _ hi

/-- **The extending labelling at a cell of the context** reads the label of the context there. -/
theorem extLabel_attachCtxCell {j : ℕ} {N : I.ALvl g H j}
    {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} (hN : N.Good B A)
    (x : Fin I.left.card) : N.extLabel (N.attEmb (I.attachCtxCell g x)) = I.left.label x := by
  rw [hN.extLabel_attEmb, attachCtxCell_eq, StageType.label_faceCell]

/-- The extending labelling at every level, for the first coatom type given up to equality. -/
theorem hasExtendingLabelLevel_of_eq {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p₀}
    {d : StageType.{u} α (n + 1)}
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ y, Q.CorrectAt t'.label y (d.label y))
    (hQ : Q.ClassCalibrated hte) (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 2 → I.HasExtendingLabelLevel g H B hdA (hI ▸ Q) j ∧
      ∀ x : Fin I.left.card,
        (I.lvLevel g H B hdA (hI ▸ Q) j).extLabel
          ((I.lvLevel g H B hdA (hI ▸ Q) j).attEmb (I.attachCtxCell g x)) = I.left.label x := by
  subst hI
  exact fun j hj ↦ ⟨hasExtendingLabelLevel hH hcard hQ hpair hB j hj,
    extLabel_attachCtxCell (lvLevel_good hH hcard hQ hB j hj)⟩

end Seed

/-! ### The test inputs -/

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **The extending labelling at the tie input**: at every seed of the input, for the requests
`req ω`, every level up to the grade `3` has a lawful labelling extending the labels of the
attachment, and at the cell of the attachment at `cellR ω` (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_tie (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 3 → I.HasExtendingLabelLevel 𝕣 H B hdA (hI ▸ req ω) j ∧
        (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) j).extLabel
          ((I.lvLevel 𝕣 H B hdA (hI ▸ req ω) j).attEmb (I.attachCtxCell 𝕣 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_ctx_root ω) hdA
    (correctAt_req ω) (classCalibrated_req ω) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨cellR.{u} ω, label_cellR ω⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

end TieInstance

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- **The extending labelling at the apex input**: at every seed of the input, for the requests
`reqTop α`, every level up to the grade `4` has a lawful labelling extending the labels of the
attachment, and at the cell of the attachment at the apex (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_apex {α : Ordinal.{u}} (I : Seed.{u} α 2)
    (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 4 → I.HasExtendingLabelLevel 𝕘 H B hdA (hI ▸ reqTop α) j ∧
        (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).extLabel
          ((I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).attEmb (I.attachCtxCell 𝕘 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_root) hdA
    (correctAt_reqTop α) (classCalibrated_reqTop α) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨apex α, label_apex α⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

end ApexInstance

namespace QuadInstance

/-- The root of the input. -/
local notation "𝕘" => root

/-- **The extending labelling at the input on four points**: at every seed of the input, for the
requests `req hα`, every level up to the grade `5` has a lawful labelling extending the labels of
the attachment, and at the cell of the attachment at the apex (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_quad {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 5 → I.HasExtendingLabelLevel 𝕘 H B hdA (hI ▸ req hα) j ∧
        (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) j).extLabel
          ((I.lvLevel 𝕘 H B hdA (hI ▸ req hα) j).attEmb (I.attachCtxCell 𝕘 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_root_quad hα) hdA
    (correctAt_req hα) (classCalibrated_req hα) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ :=
    hI ▸ ⟨apex hα, label_apex hα⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

end QuadInstance

end VaughtConjecture

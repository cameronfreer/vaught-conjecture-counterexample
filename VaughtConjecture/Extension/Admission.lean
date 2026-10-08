/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedFieldLayer
import VaughtConjecture.Extension.ProfileTowerCompletion

/-!
# Admissions: restricted catalogues at the reading grades, and recognition

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with a restricted catalogue at the
reading grades.

Let `I` be a seed.  A **state** (`Seed.State`) is a labelling of the cells of the amalgam, the old
cells of every completion.  An **admission** (`Seed.Admission`) from the grade `N` is a predicate
`Adm` on states, a bottom class `InClass`, and a predicate `CapBot` (in the instances, the states
whose private cap is `⊥`), with five laws:

* **(A1) transforms** (`Seed.Admission.map`): admitted states are closed under the transformation
  image `s ↦ min (σ ∘ s) (g ∘ grade)` of every witness `(g, σ)`, over the grading of the amalgam;
  this is the form in which locality presents a row (`Label.TransformsTo`).  It is not closure
  under `s ↦ σ ∘ s`: the shifter commutes with visibility replacement only under its suppressor.
  For capped correctness it holds when the requests are graded by the grading of the amalgam, a
  hypothesis of the instance;
* **(A2) caps** (`Seed.Admission.cap`): capping an admitted state at a label self-visible at a
  grade `k ≥ N` keeps it admitted;
* **(A0) bottom** (`Seed.Admission.bot`, `Seed.Admission.adm_of_capBot`): the constant `⊥` and
  the states of `CapBot` are admitted;
* **(A3) provision** (`Seed.Admission.provision`, the clause `Seed.CoatomProvision`): at every
  grade `k ≥ N`, `0 < k ≤ m + 1`, every state lawful below a coatom `(C, k)` agrees below `(C, k)`
  with a state `W` lawful on the grade-`k` cut (`ProfileTower.IsCutLawful`) having the
  **provision at `k`** (`Seed.ProvisionAt`): some cap `H` self-visible at `k`, at least every
  value of `W` at a cell of grade `k`, has `min (ŵ_k) H` admitted, `ŵ_k` the splice of `W` at `k`
  (`ProfileTower.hat`).

The rows allowed at the reading grades are the **reading rows** (`Seed.Admission.Row`): the
admitted states in the class, and the states of `CapBot`.  So `Adm` is the relation read back
(capped correctness, in the instances), closed under transformations, and the class enters only
through the rows of the catalogue: the implication "in the class, then admitted" is not closed under
transformations, since a witness given by locality need not reflect `⊥`, so recognition does not
transport the class and the catalogue keeps only reading rows.

**Why this form of the provision.**  Three forms are stated.

* The **literal provision** (`Seed.LiteralProvision`: the splice of every state lawful on the
  grade-`k` cut is admitted) is what the compiled lifts of the canonical layers use: each of
  `Scheme.exists_isLawfulBelow_fieldLayer`, `Scheme.exists_extension_fieldLayer`,
  `Scheme.isLawfulBelow_fieldLayer_upperDecoder`, `ProfileTower.Lvl.Good.exists_extension` and
  `ProfileTower.Lvl.Good.exists_extension_bot` extends a boundary state by a witness image of the
  row of the entry of the orbit code of the whole boundary state.
* The **boundary provision** (`Seed.BoundaryProvision`: the provision at every state lawful on the
  grade-`k` cut) is what an admitted layer needs for the extension at `⊥` from the boundary of the
  two coatoms (the boundary triple at `⊥` of `CellScheme.Rows.cappedLift_of_boundaries_short` in
  `ProfileTower.Lvl.Good.cappedLift_next` and `ProfileTower.Lvl.Good.cappedLift_top_succ`); the
  literal provision implies it (`Seed.BoundaryProvision.of_literal`).
* The **coatom provision** (`Seed.CoatomProvision`) is what bountifulness itself asks: it is
  **necessary** for every admitted completion (`CompletionBelowFullGrade.coatomProvision`), since
  the capped lift at `⊥` from one coatom extends every state lawful below it, and every labelling
  lawful below `(univ, j)`, `j ≥ N`, has the provision at its old part
  (`CompletionBelowFullGrade.provisionAt_of_isLawfulBelow`: availability at the old cells of grade
  `j`, then recognition at a cell of `(univ, j)` of largest label).  It does not prescribe the
  other coatom, so a state lawful on the cut whose capped splices are not admitted (a mixed state)
  need not be extended.

**Recognition** (`CompletionBelowFullGrade.adm_of_isLawfulBelow`).  In a completion whose rows of
full scope at the grades `≥ N` are admitted (`CompletionBelowFullGrade.HasAdmittedRows`), every
labelling `q` lawful below `(univ, j)`, `j ≥ N`, has, at every cell `u` of graded index
`(univ, j)`, the state `min (q̂_j) (q u)` admitted, `q̂_j` the splice at `j` of its old part: by
locality at `u` the row of `u` transforms to it, and by (A1).

**The admitted catalogues and layers.**  The **admitted profile catalogue**
(`ProfileTower.admittedCat`) is the set of rank-normalized profiles of the catalogue at the grade
`k` whose splices at `k` are reading rows.  Over a level `L` at the grade `g` of the tower of
rank-normalized profiles, the **layer on a sub-catalogue** `C` (`ProfileTower.Lvl.nextSOn`)
appends one cell of full scope and grade `g + 1` for each profile of `C`, with the row labelling
`ProfileTower.Lvl.ΦOn` (the section of the profile at the cells of the level, agreement heights at
the new cells); on the whole catalogue it is the next scheme of the level
(`ProfileTower.Lvl.nextSOn_cat`).  Per-entry legality (`ProfileTower.Lvl.Good.isLawfulBelow_ΦOn`),
consistency, well-formedness and coding hold for every sub-catalogue of a good level.  The
**admitted layer** (`ProfileTower.Lvl.admittedNextS`) is the layer on the admitted catalogue; its
rows of full scope are reading rows (`ProfileTower.Lvl.Good.row_rowAt_admittedNextS`), hence
admitted (`Seed.Admission.Row.adm`).  The top layer of a completion is a canonical field layer
over the level; its admitted analogue is `ProfileTower.Lvl.admittedTop`, the admitted field layer
(`Scheme.admittedFieldLayer`) for the reading rows read on the old cells.

**The trivial admission** (`Seed.Admission.all`): every state admitted and a reading row.  Its
admitted catalogue is the whole catalogue and its admitted layers are the canonical ones
(`ProfileTower.admittedCat_all`, `ProfileTower.Lvl.admittedNextS_all`,
`ProfileTower.Lvl.admittedTop_all`).

Not proved here: bountifulness of an admitted layer from the provision (the lifts of the canonical
layers do not apply, because the orbit code of a boundary state need not be admitted), and the
admitted completion.

## Placement

The engine of the restricted catalogue at the reading grades (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)"); first and second pieces.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- A **state**: a labelling of the cells of the amalgam. -/
abbrev State : Type (u + 1) := Fin I.amalgam.card → Label.{u}

/-- **The provision at a grade and a boundary state**: some cap `H` self-visible at `k`, at least
every value of `W` at a cell of grade `k`, has the splice of `W` at `k` capped at `H` admitted. -/
def ProvisionAt (Adm : I.State → Prop) (k : ℕ) (W : I.State) : Prop :=
  ∃ H : Label.{u}, IsSelfVisible k H ∧
    (∀ d, I.amalgam.toCellScheme.grade d = k → W d ≤ H) ∧
      Adm fun d ↦ min (ProfileTower.hat I k W d) H

/-- **The boundary provision from the grade `N`**: the provision at every grade `k ≥ N` and every
state lawful on the grade-`k` cut, the boundary of the two coatoms at `k`.  It is what the
extension at `⊥` from the boundary of the two coatoms asks of an admitted layer. -/
def BoundaryProvision (N : ℕ) (Adm : I.State → Prop) : Prop :=
  ∀ ⦃k : ℕ⦄, N ≤ k → ∀ ⦃W : I.State⦄, ProfileTower.IsCutLawful I k W → I.ProvisionAt Adm k W

/-- **The coatom provision from the grade `N`**: at every grade `k ≥ N` with `0 < k ≤ m + 1` and
either coatom `C`, every state lawful below `(C, k)` agrees below `(C, k)` with a state lawful on
the grade-`k` cut that has the provision at `k`.  It is what the capped lift at `⊥` from one coatom
into the full face asks of an admitted completion (`CompletionBelowFullGrade.coatomProvision`). -/
def CoatomProvision (N : ℕ) (Adm : I.State → Prop) : Prop :=
  ∀ ⦃k : ℕ⦄, N ≤ k → 0 < k → k ≤ m + 1 → ∀ ⦃x : Fin (m + 2)⦄,
    x ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) → ∀ ⦃W : I.State⦄,
      I.amalgam.rows.IsLawfulBelow (univ.erase x, k) (fun d ↦ W d) →
      ∃ W' : I.State, ProfileTower.IsCutLawful I k W' ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W' d = W d) ∧
          I.ProvisionAt Adm k W'

/-- **Closure under transformation images** over the grading of the amalgam: for every witness
`(g, σ)`, the state `d ↦ min (σ (s d)) (g (grade d))` is admitted when `s` is. -/
def IsTransformClosed (Adm : I.State → Prop) : Prop :=
  ∀ ⦃s : I.State⦄ ⦃g : ℕ → Label.{u}⦄ ⦃σ : Label.{u} → Label.{u}⦄, Adm s → IsWitness g σ →
    Adm fun d ↦ min (σ (s d)) (g (I.amalgam.toCellScheme.grade d))

/-- **The literal provision from the grade `N`**: the splice at `k` of every state lawful on the
grade-`k` cut is admitted, for every `k ≥ N`.  It is what the compiled lifts of the canonical layers
use. -/
def LiteralProvision (N : ℕ) (Adm : I.State → Prop) : Prop :=
  ∀ ⦃k : ℕ⦄, N ≤ k → ∀ ⦃W : I.State⦄, ProfileTower.IsCutLawful I k W →
    Adm (ProfileTower.hat I k W)

variable {I}

/-- **At a state with a top at the grade `k`, the provision is admission of the splice**: the cap
must be `⊤`.  So a state lawful on the cut, `⊤` at a cell of grade `k`, whose splice is not
admitted (the mixed state of a seed of a type with itself, under capped correctness) refutes the
boundary provision. -/
theorem provisionAt_iff_of_eq_top {Adm : I.State → Prop} {k : ℕ} {W : I.State}
    {d₀ : Fin I.amalgam.card} (hd₀ : I.amalgam.toCellScheme.grade d₀ = k) (htop : W d₀ = ⊤) :
    I.ProvisionAt Adm k W ↔ Adm (ProfileTower.hat I k W) := by
  refine ⟨fun ⟨H, _, hle, hA⟩ ↦ ?_, fun h ↦ ⟨⊤, isSelfVisible_top _, fun _ _ ↦ le_top,
    by simpa only [min_top_right] using h⟩⟩
  obtain rfl : H = ⊤ := top_le_iff.mp (htop ▸ hle d₀ hd₀)
  simpa only [min_top_right] using hA

/-- **The literal provision implies the boundary provision**, at the cap `⊤`. -/
theorem BoundaryProvision.of_literal {N : ℕ} {Adm : I.State → Prop}
    (h : I.LiteralProvision N Adm) : I.BoundaryProvision N Adm := fun _ hk W hW ↦
  ⟨⊤, isSelfVisible_top _, fun _ _ ↦ le_top, by simpa only [min_top_right] using h hk hW⟩

end Seed

/-! ### Recognition -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (N : ℕ) (Adm : I.State → Prop)

/-- The **row state** of a cell `u`: its row read at the old cells (`⊥` at those not below it). -/
noncomputable def rowState (u : Fin F.scheme.card) : I.State := fun d ↦ F.scheme.rowAt u (F.embed d)

/-- The completion **has admitted rows** from the grade `N`: the row state of every cell of graded
index `(univ, j)` with `j ≥ N` is admitted. -/
def HasAdmittedRows : Prop :=
  ∀ ⦃u : Fin F.scheme.card⦄ ⦃j : ℕ⦄, F.scheme.toCellScheme.gradedIndex u = (univ, j) → N ≤ j →
    Adm (F.rowState u)

variable {F N Adm}

/-- **Recognition.**  In a completion with admitted rows, let `q` be lawful below `(univ, j)`,
`j ≥ N`, and `u` a cell of graded index `(univ, j)`.  Then the splice at `j` of the old part of
`q`, capped at `q u`, is admitted: by locality at `u` the row of `u` transforms to it, and admitted
states are closed under transformation witnesses (A1). -/
theorem adm_of_isLawfulBelow (hmap : I.IsTransformClosed Adm) (hF : F.HasAdmittedRows N Adm)
    {j : ℕ} (hj : N ≤ j)
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun z ↦ q z)
    {u : Fin F.scheme.card} (hu : F.scheme.toCellScheme.gradedIndex u = (univ, j)) :
    Adm fun d ↦ min (ProfileTower.hat I j (fun e ↦ q (F.embed e)) d) (q u) := by
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hq
  obtain ⟨g, σ, hw, heq⟩ := hloc u (by rw [CellScheme.mem_below, hu])
  convert hmap (hF hu hj) hw using 1
  funext d
  have hgi := F.gradedIndex_embed d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
  · have hmem : F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact ⟨subset_univ _, hd⟩
    rw [ProfileTower.hat_of_le hd, rowState, Scheme.rowAt_of_mem hmem,
      ← F.isLowerEmbedding.grade_eq d]
    exact heq ⟨F.embed d, hmem⟩
  · have hmem : F.embed d ∉ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact fun h ↦ hd h.2
    rw [ProfileTower.hat_of_lt (not_le.mp hd), rowState, Scheme.rowAt_of_notMem hmem, hw.map_bot,
      min_bot_left, min_bot_left]

/-- **The provision is necessary for an admitted completion.**  In a completion with admitted rows
carrying a cell at `(univ, j)`, `j ≥ N`, every labelling `q` lawful below `(univ, j)` has the
provision at the grade `j` at every state `W` agreeing with its old part at the cells of grade at
most `j`: the cap is the largest label of `q` at the cells of `(univ, j)`, at least every value
of `q` at an old cell of grade `j` by availability, and the capped splice is admitted by
recognition at a cell carrying it. -/
theorem provisionAt_of_isLawfulBelow (hmap : I.IsTransformClosed Adm)
    (hF : F.HasAdmittedRows N Adm) {j : ℕ} (hj : N ≤ j)
    (hex : ∃ u, F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), j))
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun z ↦ q z)
    {W : I.State} (hW : ∀ d, I.amalgam.toCellScheme.grade d ≤ j → q (F.embed d) = W d) :
    I.ProvisionAt Adm j W := by
  classical
  obtain ⟨ho, -, hav⟩ := Rows.isLawfulBelow_iff_forall.mp hq
  set U := univ.filter fun z : Fin F.scheme.card ↦
    F.scheme.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j)
  obtain ⟨u₀, hu₀⟩ := hex
  obtain ⟨u, huU, hmax⟩ := U.exists_max_image q ⟨u₀, by simpa [U] using hu₀⟩
  have hu : F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), j) := by
    simpa [U] using huU
  have hub : u ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hu]
  have hgu : F.scheme.toCellScheme.grade u = j := congrArg Prod.snd hu
  have hhat : ProfileTower.hat I j (fun e ↦ q (F.embed e)) = ProfileTower.hat I j W := by
    funext d
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
    · rw [ProfileTower.hat_of_le hd, ProfileTower.hat_of_le hd, hW d hd]
    · rw [ProfileTower.hat_of_lt (not_le.mp hd), ProfileTower.hat_of_lt (not_le.mp hd)]
  refine ⟨q u, hgu ▸ ho u hub, fun d hd ↦ ?_, ?_⟩
  · have hsc : F.scheme.toCellScheme.scope (F.embed d) ⊆ F.scheme.toCellScheme.scope u := by
      have hsu : F.scheme.toCellScheme.scope u = univ := congrArg Prod.fst hu
      rw [hsu]
      exact subset_univ _
    have hg : F.scheme.toCellScheme.grade (F.embed d) = F.scheme.toCellScheme.grade u := by
      rw [F.isLowerEmbedding.grade_eq d, hd, hgu]
    obtain ⟨v, hv, hle⟩ := hav (F.embed d) u hub hsc hg
    rw [← hW d hd.le]
    exact hle.trans (hmax v (by simpa [U, hu] using hv))
  · have h := adm_of_isLawfulBelow hmap hF hj hq hu
    rwa [hhat] at h


/-- **The coatom provision is necessary for an admitted completion.**  In a completion with admitted
rows from the grade `N`, admitted states closed under transformation images, every state `W`
lawful below a coatom `(C, k)`, `N ≤ k`, `0 < k ≤ m + 1`, agrees below `(C, k)` with a state
lawful on the grade-`k` cut having the provision at `k`: the capped lift at `⊥` from `(C, k)` into
`(univ, k)` (bountifulness of the completion) extends `W` to a labelling lawful below `(univ, k)`,
whose old part has the provision (`CompletionBelowFullGrade.provisionAt_of_isLawfulBelow`). -/
theorem coatomProvision (hmap : I.IsTransformClosed Adm) (hF : F.HasAdmittedRows N Adm) :
    I.CoatomProvision N Adm := by
  classical
  intro k hN hk0 hkm x hx W hW
  have hL := F.isLegalBelowFullGrade
  have hne : univ.erase x ≠ univ := Seed.ne_univ_erase x
  have hfaces := F.faces_eq
  have hX : (univ.erase x, k) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨hfaces ▸ I.erase_mem_faces hx, hk0, by simp only; rw [Seed.card_erase]; exact hkm⟩
  have hY : ((univ : Finset (Fin (m + 2))), k) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨hL.isWellFormed.univ_mem_faces, hk0, by simp only [card_univ, Fintype.card_fin]; omega⟩
  have hXY : ((univ.erase x, k) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, k) :=
    ⟨erase_subset _ _, le_rfl⟩
  -- The state, carried to the cells of the completion.
  set w : Fin F.scheme.card → Label.{u} := Function.extend F.embed W fun _ ↦ ⊥ with hw
  have hwe (d : Fin I.amalgam.card) : w (F.embed d) = W d := F.embed.injective.extend_apply _ _ d
  have hwX : F.scheme.rows.IsLawfulBelow (univ.erase x, k) fun z ↦ w z := by
    rw [F.isLawfulBelow_embed_iff hne]
    simpa only [hwe] using hW
  obtain ⟨q', ⟨hq', -⟩, hq'w⟩ := hL.isBountiful hX hY hXY ⊥ (isSelfVisible_bot k)
    (fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _) ⟨hwX, fun _ ↦ by simp⟩
  set q : Fin F.scheme.card → Label.{u} := Rows.extendBot ((univ : Finset (Fin (m + 2))), k) q'
  have hqq' (z : F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), k)) : q z = q' z :=
    Rows.extendBot_of_mem q' z.2
  have hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) fun z ↦ q z := by
    convert hq' using 1
    exact funext hqq'
  have hcut (y : Fin (m + 2)) :
      I.amalgam.rows.IsLawfulBelow (univ.erase y, k) fun d ↦ q (F.embed d) :=
    (F.isLawfulBelow_embed_iff (Seed.ne_univ_erase y)).mp
      (hq.mono (X := (univ.erase y, k)) ⟨erase_subset _ _, le_rfl⟩)
  have hex := hL.exists_gradedIndex_eq _ hY (by simp only; omega)
  refine ⟨fun d ↦ q (F.embed d), ⟨hcut _, hcut _⟩, fun d hd ↦ ?_,
    provisionAt_of_isLawfulBelow hmap hF hN hex hq fun _ _ ↦ rfl⟩
  have hdX : F.embed d ∈ F.scheme.toCellScheme.below (univ.erase x, k) := by
    rw [CellScheme.mem_below, F.gradedIndex_embed]
    exact hd
  have h := congrFun hq'w ⟨F.embed d, hdX⟩
  simp only [Function.comp_apply] at h
  rw [← hwe d, ← h, ← hqq']

end CompletionBelowFullGrade

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

variable (I) in
/-- **An admission from the grade `N`**: a predicate `Adm` on states, closed under transformation
images (A1) and caps at grades `≥ N` (A2), holding at the constant `⊥` (A0), with the provision
(A3); a bottom class `InClass` and a predicate `CapBot` (the states whose private cap is `⊥`),
admitted unconditionally.  The rows allowed at the reading grades are the **reading rows**
(`Seed.Admission.Row`): admitted states in the class, and the states of `CapBot`. -/
structure Admission where
  /-- The least grade at which the rows of full scope are restricted. -/
  N : ℕ
  /-- The admitted states. -/
  Adm : I.State → Prop
  /-- The bottom class of the rows at the reading grades. -/
  InClass : I.State → Prop
  /-- The states admitted unconditionally (private cap `⊥`). -/
  CapBot : I.State → Prop
  /-- (A1) Admitted states are closed under transformation images over the grading of the
  amalgam. -/
  map : I.IsTransformClosed Adm
  /-- (A2) Capping at a label self-visible at a grade `k ≥ N` keeps admission. -/
  cap : ∀ ⦃s : I.State⦄ ⦃k : ℕ⦄ ⦃h : Label.{u}⦄, N ≤ k → Adm s → IsSelfVisible k h →
    Adm fun d ↦ min (s d) h
  /-- (A0) The constant `⊥` is admitted. -/
  bot : Adm fun _ ↦ ⊥
  /-- (A0) The states of `CapBot` are admitted. -/
  adm_of_capBot : ∀ ⦃s : I.State⦄, CapBot s → Adm s
  /-- (A3) The coatom provision from the grade `N`. -/
  provision : I.CoatomProvision N Adm

namespace Admission

variable (A : I.Admission)

/-- A **reading row**: an admitted state in the class, or a state of `CapBot`. -/
def Row (s : I.State) : Prop := (A.InClass s ∧ A.Adm s) ∨ A.CapBot s

variable {A} in
/-- **A reading row is admitted.** -/
theorem Row.adm {s : I.State} (h : A.Row s) : A.Adm s :=
  h.elim (fun h ↦ h.2) fun h ↦ A.adm_of_capBot h

/-- **The splice of an admitted state is admitted** (A1, at the step witness). -/
theorem adm_hat {s : I.State} (hs : A.Adm s) (k : ℕ) : A.Adm (ProfileTower.hat I k s) := by
  convert A.map hs (IsWitness.id_step k) using 1
  funext d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [ProfileTower.hat_of_le hd, stepSuppressor_of_le hd, id, min_top_right]
  · rw [ProfileTower.hat_of_lt (not_le.mp hd), stepSuppressor_of_lt (not_le.mp hd), min_bot_right]

variable (I) in
/-- **The trivial admission** from the grade `N`: every state is admitted, in the class, and
admitted unconditionally.  Its coatom provision is that of the canonical completion
(`Seed.nonempty_completionBelowFullGrade`, `CompletionBelowFullGrade.coatomProvision`). -/
def all (N : ℕ) : I.Admission where
  N := N
  Adm _ := True
  InClass _ := True
  CapBot _ := True
  map _ _ _ _ _ := trivial
  cap _ _ _ _ _ _ := trivial
  bot := trivial
  adm_of_capBot _ _ := trivial
  provision := (I.nonempty_completionBelowFullGrade.some).coatomProvision
    (fun _ _ _ _ _ ↦ trivial) fun _ _ _ _ ↦ trivial

/-- Every state is a reading row of the trivial admission. -/
theorem row_all (N : ℕ) (s : I.State) : (all I N).Row s := .inr trivial

end Admission

end Seed

/-! ### The admitted profile catalogue and the layers on sub-catalogues -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

open Classical in
/-- The **profile catalogue of a predicate** `Rw` on states at the grade `k`: the rank-normalized
profiles of the catalogue at `k` whose splices at `k` satisfy `Rw`. -/
noncomputable def rowCat (Rw : I.State → Prop) (k : ℕ) : Finset (Prof I) :=
  (cat I k).filter fun R ↦ Rw (hat I k R)

/-- The **admitted profile catalogue** at the grade `k`: the rank-normalized profiles of the
catalogue at `k` whose splices at `k` are reading rows. -/
noncomputable def admittedCat (A : I.Admission) (k : ℕ) : Finset (Prof I) := rowCat A.Row k

theorem mem_rowCat {Rw : I.State → Prop} {k : ℕ} {R : Prof I} :
    R ∈ rowCat Rw k ↔ R ∈ cat I k ∧ Rw (hat I k R) := by
  classical
  simp only [rowCat, Finset.mem_filter]

theorem mem_admittedCat {A : I.Admission} {k : ℕ} {R : Prof I} :
    R ∈ admittedCat A k ↔ R ∈ cat I k ∧ A.Row (hat I k R) :=
  mem_rowCat

theorem admittedCat_subset (A : I.Admission) (k : ℕ) : admittedCat A k ⊆ cat I k :=
  fun _ hR ↦ (mem_admittedCat.mp hR).1

/-- The constant `⊥` is an admitted profile when it is a reading row. -/
theorem bot_mem_admittedCat (A : I.Admission) (k : ℕ) (hA : A.Row fun _ ↦ ⊥) :
    (fun _ ↦ ⊥ : Prof I) ∈ admittedCat A k := by
  refine mem_admittedCat.mpr ⟨bot_mem_cat k, ?_⟩
  convert hA using 1
  funext d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · exact hat_of_le hd
  · exact hat_of_lt (_root_.not_le.mp hd)

/-- **The admitted catalogue of the trivial admission is the whole catalogue.** -/
theorem admittedCat_all (N k : ℕ) : admittedCat (Seed.Admission.all I N) k = cat I k := by
  classical
  exact Finset.filter_true_of_mem fun _ _ ↦ Seed.Admission.row_all N _

/-- The profile of the new cell `i` of the layer on `C`. -/
noncomputable def entryOn (C : Finset (Prof I)) (i : Fin C.card) : Prof I := (C.equivFin.symm i).1

theorem entryOn_mem {C : Finset (Prof I)} (i : Fin C.card) : entryOn C i ∈ C :=
  (C.equivFin.symm i).2

theorem exists_entryOn_eq {C : Finset (Prof I)} {R : Prof I} (hR : R ∈ C) :
    ∃ i, entryOn C i = R :=
  ⟨C.equivFin ⟨R, hR⟩, by simp [entryOn]⟩

section Step

variable {g : ℕ} (L : Lvl I g) (C : Finset (Prof I))

/-- The row labelling of the layer on `C` at the grade `g + 1`: the section of `R` at the cells of
the level, and the agreement heights of `R` with the profiles of `C`. -/
noncomputable def Lvl.ΦOn (R : Prof I) : Fin (L.S.card + C.card) → Label.{u} :=
  Fin.append (L.σ R) fun i ↦ agreementHeight (grid (g + 1) (bound I)) R (entryOn C i)

/-- **The layer on a sub-catalogue** `C` over a level at the grade `g`: the level followed by one
cell at `(univ, g + 1)` per profile of `C`, with the row labelling of its profile. -/
noncomputable abbrev Lvl.nextSOn : Scheme.{u} (m + 2) :=
  L.S.appendFullCells (g + 1) C.card (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le

/-- **On the whole catalogue, the layer on `C` is the next scheme of the level.** -/
theorem Lvl.nextSOn_cat : L.nextSOn (cat I (g + 1)) = L.nextS := rfl

variable {L C}

@[simp] theorem Lvl.ΦOn_castAdd (R : Prof I) (e : Fin L.S.card) :
    L.ΦOn C R (Fin.castAdd _ e) = L.σ R e := Fin.append_left _ _ e

@[simp] theorem Lvl.ΦOn_natAdd (R : Prof I) (i : Fin C.card) :
    L.ΦOn C R (Fin.natAdd _ i) = agreementHeight (grid (g + 1) (bound I)) R (entryOn C i) :=
  Fin.append_right _ _ i

theorem Lvl.Good.ΦOn_mem_codeGrid (hL : L.Good) {R : Prof I}
    (hR : ∀ d, R d ∈ codeGrid (g + 1) (bound I)) (z : Fin (L.S.card + C.card)) :
    L.ΦOn C R z ∈ codeGrid (g + 1) (bound I) := by
  induction z using Fin.addCases with
  | left e => rw [Lvl.ΦOn_castAdd]; exact hL.mem R hR e
  | right i =>
    rw [Lvl.ΦOn_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Lawfulness below a pair not above `(univ, g + 1)` in the layer on `C` is lawfulness in the
level. -/
theorem Lvl.isLawfulBelow_nextSOn_iff {X : Finset (Fin (m + 2)) × ℕ}
    (hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X)
    {v : Fin (L.S.card + C.card) → Label.{u}} :
    (L.nextSOn C).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      L.S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  Scheme.isLawfulBelow_appendFullCells_iff hX

/-- **Per-entry legality**: the row labelling on `C` of a profile of the catalogue at `g + 1` that
lies in `C` is lawful below `(univ, g + 1)` in the layer on `C`. -/
theorem Lvl.Good.isLawfulBelow_ΦOn (hL : L.Good) {R : Prof I} (hR : R ∈ cat I (g + 1))
    (hRC : R ∈ C) :
    (L.nextSOn C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1)
      fun z ↦ L.ΦOn C R z := by
  classical
  obtain ⟨⟨hC, hD⟩, -⟩ := mem_cat.mp hR
  have hRB := mem_codeGrid_of_mem_cat hR
  have hlow : (L.nextSOn C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g)
      fun z ↦ L.ΦOn C R z := by
    refine (Lvl.isLawfulBelow_nextSOn_iff (by rintro ⟨-, h⟩; simp only at h; omega)).mpr ?_
    simpa only [Lvl.ΦOn_castAdd] using hL.lawful R ⟨hC.mono (X := (_, g)) ⟨subset_rfl, by omega⟩,
      hD.mono (X := (_, g)) ⟨subset_rfl, by omega⟩⟩
  have hcoat (x : Fin (m + 2))
      (hRX : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ R d) :
      (L.nextSOn C).rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ L.ΦOn C R z := by
    refine (Lvl.isLawfulBelow_nextSOn_iff fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1)).mpr ?_
    simp only [Lvl.ΦOn_castAdd]
    rw [hL.isLawfulBelow_old_iff (Seed.ne_univ_erase x)]
    exact (Rows.isLawfulBelow_congr (w' := fun d ↦ L.σ R (L.embed d))
      fun d _ ↦ (hL.literal R d).symm).mp hRX
  have hcC := hcoat _ hC
  have hcD := hcoat _ hD
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp hlow
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hcC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hcD
  have hcases {e : Fin L.S.card}
      (he : Fin.castAdd C.card e ∈
        (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      Fin.castAdd C.card e ∈ (L.nextSOn C).toCellScheme.below (coatC, g + 1) ∨
        Fin.castAdd C.card e ∈
          (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g) ∨
        Fin.castAdd C.card e ∈ (L.nextSOn C).toCellScheme.below (coatD, g + 1) := by
    have he' : e ∈ L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
      have := he
      rwa [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hL.mem_below_cover (by simp) (by simp) Seed.last_ne_castSucc e he'
  obtain ⟨i₀, hi₀⟩ := exists_entryOn_eq hRC
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [hoC _ h, ho2 _ h, hoD _ h]
    | right j =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, Lvl.ΦOn_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hlC _ h, hl2 _ h, hlD _ h]
    | right j =>
      set κ := agreementHeight (grid (g + 1) (bound I)) R (entryOn C j) with hκ
      have hκm : κ ∈ grid (g + 1) (bound I) := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible (g + 1) κ := isSelfVisible_of_mem_grid hκm
      refine ⟨constStepSuppressor (g + 1) κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : (L.nextSOn C).toCellScheme.grade t ≤ g + 1 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) _ j))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, Lvl.ΦOn_natAdd]
      obtain ⟨t, -⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [Lvl.ΦOn_castAdd, Lvl.ΦOn_castAdd]
        exact hL.capAgree R (entryOn C j) hRB κ hκv (isShort_of_mem_grid hκm)
          (agreementHeight_spec (bot_mem_grid _ _) R (entryOn C j)).2 e
      | right j' =>
        rw [Lvl.ΦOn_natAdd, Lvl.ΦOn_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [haC s _ h hst hg, ha2 s _ h hst hg, haD s _ h hst hg]
    | right j =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [Lvl.ΦOn_natAdd, hi₀, agreementHeight_self_ceiling']
      exact le_gridPoint_of_mem_codeGrid (hL.ΦOn_mem_codeGrid hRB s)

/-- **The layer on a sub-catalogue of a good level is consistent.** -/
theorem Lvl.Good.isConsistent_nextSOn (hL : L.Good) (hC : C ⊆ cat I (g + 1)) :
    (L.nextSOn C).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    have hu := Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) C.card i
    have h := hL.isLawfulBelow_ΦOn (hC (entryOn_mem i)) (entryOn_mem i)
    rw [Scheme.appendFullCells_row_natAdd_eq]
    rw [show (L.nextSOn C).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin (m + 2))), g + 1) from hu]
    exact h
  | left s =>
    have hφ := Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) C.card
      (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [Scheme.comap_rows_castAdd]
    convert hL.consistent s using 1
    funext t
    exact congrArg (fun R : L.S.toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd

/-- **The layer on `C` over a good level is well formed**, for `g + 1 ≤ m + 2`. -/
theorem Lvl.Good.isWellFormed_nextSOn (hL : L.Good) (hg : g + 1 ≤ m + 2) :
    (L.nextSOn C).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells hL.wf (by omega) hg

/-- **The layer on a sub-catalogue of a good level is coded.** -/
theorem Lvl.Good.isCoded_nextSOn (hL : L.Good) (hC : C ⊆ cat I (g + 1)) :
    (L.nextSOn C).IsCoded :=
  Scheme.isCoded_appendFullCells hL.coded fun i d ↦ lt_omega0_sq_of_mem_codeGrid
    (hL.ΦOn_mem_codeGrid (mem_codeGrid_of_mem_cat (hC (entryOn_mem i))) d)

/-- A cell of the layer on `C` of graded index `(univ, g + 1)` is new. -/
theorem Lvl.exists_natAdd_eq_nextSOn {u : Fin (L.nextSOn C).card}
    (hu : (L.nextSOn C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, Fin.natAdd _ i = u := by
  by_cases hlt : (u : ℕ) < L.S.card
  · refine absurd ?_ (L.not_le ⟨u, hlt⟩)
    rw [← Scheme.appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < L.S.card + C.card := u.2
    exact ⟨⟨u - L.S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- The old cells of the layer on `C`. -/
noncomputable def Lvl.embedOn (L : Lvl I g) (C : Finset (Prof I)) :
    Fin I.amalgam.card ↪o Fin (L.nextSOn C).card :=
  L.embed.trans (Fin.castAddOrderEmb _)

/-- **The row of a cell of the layer on `C` of graded index `(univ, g + 1)`, read at the old cells,
is the splice at `g + 1` of its profile.** -/
theorem Lvl.Good.rowAt_nextSOn (hL : L.Good) {u : Fin (L.nextSOn C).card}
    (hu : (L.nextSOn C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ R ∈ C, ∀ d, (L.nextSOn C).rowAt u (L.embedOn C d) = hat I (g + 1) R d := by
  obtain ⟨i, rfl⟩ := Lvl.exists_natAdd_eq_nextSOn hu
  refine ⟨entryOn C i, entryOn_mem i, fun d ↦ ?_⟩
  have hgi : (L.nextSOn C).toCellScheme.gradedIndex (L.embedOn C d) =
      I.amalgam.toCellScheme.gradedIndex d :=
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (hL.gradedIndex_embed d)
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
  · have hmem : L.embedOn C d ∈ (L.nextSOn C).toCellScheme.below
        ((L.nextSOn C).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact ⟨subset_univ _, hd⟩
    rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, hat_of_le hd]
    change L.ΦOn C (entryOn C i) (Fin.castAdd _ (L.embed d)) = _
    rw [Lvl.ΦOn_castAdd, hL.literal]
  · have hmem : L.embedOn C d ∉ (L.nextSOn C).toCellScheme.below
        ((L.nextSOn C).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact fun h ↦ hd h.2
    rw [Scheme.rowAt_of_notMem hmem, hat_of_lt (_root_.not_le.mp hd)]

variable (L) in
/-- **The admitted layer** over a level at the grade `g`: the layer on the admitted catalogue at
the grade `g + 1`. -/
noncomputable abbrev Lvl.admittedNextS (A : I.Admission) : Scheme.{u} (m + 2) :=
  L.nextSOn (admittedCat A (g + 1))

/-- **For the trivial admission, the admitted layer is the next scheme of the level.** -/
theorem Lvl.admittedNextS_all (N : ℕ) : L.admittedNextS (Seed.Admission.all I N) = L.nextS := by
  rw [Lvl.admittedNextS, admittedCat_all, Lvl.nextSOn_cat]

/-- **The admitted layer over a good level is consistent.** -/
theorem Lvl.Good.isConsistent_admittedNextS (hL : L.Good) (A : I.Admission) :
    (L.admittedNextS A).rows.IsConsistent :=
  hL.isConsistent_nextSOn (admittedCat_subset A _)

/-- **The admitted layer over a good level is coded.** -/
theorem Lvl.Good.isCoded_admittedNextS (hL : L.Good) (A : I.Admission) :
    (L.admittedNextS A).IsCoded :=
  hL.isCoded_nextSOn (admittedCat_subset A _)

/-- **The admitted layer carries a cell at `(univ, g + 1)`**, the cell of the constant `⊥`, when it
is a reading row. -/
theorem Lvl.exists_gradedIndex_eq_admittedNextS (A : I.Admission) (hA : A.Row fun _ ↦ ⊥) :
    ∃ u, (L.admittedNextS A).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), g + 1) := by
  obtain ⟨i, -⟩ := exists_entryOn_eq (bot_mem_admittedCat A (g + 1) hA)
  exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩

/-- **The rows of full scope of the admitted layer are reading rows**, read at the old cells. -/
theorem Lvl.Good.row_rowAt_admittedNextS (hL : L.Good) (A : I.Admission)
    {u : Fin (L.admittedNextS A).card}
    (hu : (L.admittedNextS A).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), g + 1)) :
    A.Row fun d ↦ (L.admittedNextS A).rowAt u (L.embedOn (admittedCat A (g + 1)) d) := by
  obtain ⟨R, hR, hrow⟩ := hL.rowAt_nextSOn hu
  rw [funext hrow]
  exact (mem_admittedCat.mp hR).2

end Step

/-! ### The admitted top layer -/

/-- **The admitted top layer** over a level at the grade `m`: the admitted field layer at the grade
`m + 1` for the reading rows, read on the old cells. -/
noncomputable abbrev Lvl.admittedTop (N : Lvl I m) (A : I.Admission) : Scheme.{u} (m + 2) :=
  N.S.admittedFieldLayer (m + 1) (fun e ↦ A.Row (hat I (m + 1) fun d ↦ e (N.embed d))) N.not_le

/-- **For the trivial admission, the admitted top layer is the top layer.** -/
theorem Lvl.admittedTop_all (N : Lvl I m) (K : ℕ) :
    N.admittedTop (Seed.Admission.all I K) = N.top :=
  Scheme.admittedFieldLayer_of_forall fun _ ↦ Seed.Admission.row_all K _

end ProfileTower


end VaughtConjecture

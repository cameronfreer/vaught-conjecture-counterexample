/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachmentMirror
import VaughtConjecture.Extension.CapTransport

/-!
# The writing of a state in the replicated scheme, and lifts from writings

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

The **writing** of a state `R` of the attachment in the replicated scheme
(`Seed.replicatedWriting`) is the writing of `R` in the ladder tower over the attachment, every copy
reading it at its original.  For a state of the catalogue at the grade `m + 2` it is a lawful
section of the replicated scheme (`Seed.isLawful_replicatedWriting`: the writing is lawful on the
tower, and lawful sections pull back through the originals, the mirroring being saturated), and it
is the state at the cells of the attachment (`Seed.replicatedWriting_attachEmb`).  Its decoding by
a witness bounded by a grade that sends no non-bottom label to bottom is lawful below every pair of
that grade (`Seed.isLawfulBelow_map_replicatedWriting`).

**Lifts from writings** (`Seed.cappedLift_replicated_of_writingLift`).  The replicated scheme lifts
capped from `X` to `Y` when every lift problem is solved by a decoded writing
(`Seed.WritingLift X Y`): a state of the catalogue and a decoder whose decoded writing reads the
prescription below `X` and keeps the observation of the ambient at the cap below `Y`.  This is the
common form of the lifts left open in `VaughtConjecture.MainTheorem.ReplicatedInputs`: from the
context coatom (a state lift on the attachment and the coding of states), from the mixed coatom and
into the mixed faces (in addition, the prescription at the copies must be read as a decoded writing:
the recognition of the state on the copies).

## References

Lawful sections, consistency and bountifulness are [Kni26, Definitions 2.5.4, 2.5.12 and 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (I g H Γ A B') in
/-- **The writing of a state in the replicated scheme**: the writing in the ladder tower over the
attachment, every copy reading it at its original. -/
noncomputable def replicatedWriting (R : Fin (I.attachment g).card → Label.{u}) :
    Fin (I.replicated g H Γ A B').card → Label.{u} :=
  fun z ↦ ((I.attachmentBase g).ladderTower H Γ A B' m).v R
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z)

/-- **The writing of a state of the catalogue is lawful on the replicated scheme.** -/
theorem isLawful_replicatedWriting (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {R : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (m + 2)) :
    (I.replicated g H Γ A B').rows.IsLawful (I.replicatedWriting g H Γ A B' R) :=
  (Scheme.mirrorData (I.not_subset_scope_tower g H Γ A B')).isLawful_comp
    ((Scheme.LadderBaseData.ladderTower_lawful hH hcard hΓ hA m).2 R hR).1
    (Scheme.saturated_mirrorData _)

/-- **The writing of a lawful state is the state at the cells of the attachment.** -/
theorem replicatedWriting_attachEmb (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (c : Fin (I.attachment g).card) :
    I.replicatedWriting g H Γ A B' R (I.attachEmb g H Γ A B' c) = R c := by
  change ((I.attachmentBase g).ladderTower H Γ A B' m).v R
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = R c
  rw [Scheme.mirrorOrig_castAdd]
  refine (Scheme.layerTower_v_emb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') R _ m).trans ?_
  exact Scheme.LadderBaseData.stateExt_castAdd hR hcard c

/-- **The decoded writing of a state of the catalogue is lawful** below every pair of the grade of
the decoder, for a witness that sends no non-bottom label to bottom. -/
theorem isLawfulBelow_map_replicatedWriting (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {R : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (m + 2)) (Y : Finset (Fin (m + 2)) × ℕ)
    {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor Y.2) ν)
    (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    (I.replicated g H Γ A B').rows.IsLawfulBelow Y
      fun d ↦ ν (I.replicatedWriting g H Γ A B' R d) :=
  ((isLawful_replicatedWriting hH hcard hΓ hA hR).isLawfulBelow Y).map_of_apply_eq_bot
    (fun d ↦ d.2.2) hν fun _ h ↦ hbot _ h

variable (I g H Γ A B') in
/-- **Lifts by decoded writings** from `X` to `Y`: for every cap `c` self-visible at the grade of
`Y`, prescription `p` lawful below `X` and ambient `q` lawful below `Y` with the same observation at
`c`, some state of the catalogue at the grade `m + 2` and some witness `ν` bounded by the grade of
`Y` sending no non-bottom label to bottom have a decoded writing reading `p` below `X` and the
observation of `q` at `c` below `Y`. -/
def WritingLift (X Y : Finset (Fin (m + 2)) × ℕ) (hXY : X ≤ Y) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible Y.2 c →
    ∀ (p : (I.replicated g H Γ A B').toCellScheme.below X → Label.{u})
      (q : (I.replicated g H Γ A B').toCellScheme.below Y → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow X p →
      (I.replicated g H Γ A B').rows.IsLawfulBelow Y q →
      (∀ d, min (q (Set.inclusion (CellScheme.below_mono _ hXY) d)) c = min (p d) c) →
      ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2), ∃ ν : Label.{u} → Label.{u},
        IsWitness (stepSuppressor Y.2) ν ∧ (∀ x, ν x = ⊥ → x = ⊥) ∧
        (∀ d : (I.replicated g H Γ A B').toCellScheme.below X,
          ν (I.replicatedWriting g H Γ A B' R d) = p d) ∧
        ∀ d : (I.replicated g H Γ A B').toCellScheme.below Y,
          min (ν (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c

/-- **The replicated scheme lifts capped wherever decoded writings solve the lift problems.** -/
theorem cappedLift_replicated_of_writingLift (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hw : I.WritingLift g H Γ A B' X Y hXY) : (I.replicated g H Γ A B').rows.CappedLift hXY := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨R, hR, ν, hν, hbot, hνp, hνq⟩ := hw c hc p q hp hq hpq
  exact ⟨fun d ↦ ν (I.replicatedWriting g H Γ A B' R d),
    isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hR Y hν hbot, hνq,
    fun d ↦ hνp d⟩

/-! ### The copies read the controllers -/

/-- **A lawful section reads, at a cell whose original is a cell of full scope at a grade
`N + 2 ≤ m + 1`, a witness image of the state of that controller** on the cells of the attachment
inside its scope: the cell's row is the controller's row, which stores the state (a copy reads
the row of its original).  This is the first step of the recognition on the copies. -/
theorem exists_copy_reading (hcard : (I.attachmentBase g).S.card ≤ H)
    {Y : Finset (Fin (m + 2)) × ℕ} {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow Y fun d ↦ w d)
    {k : Fin (I.replicated g H Γ A B').card}
    (hk : k ∈ (I.replicated g H Γ A B').toCellScheme.below Y) {N : ℕ} (hN : N + 1 ≤ m)
    (hko : (I.attachTower g H Γ A B').toCellScheme.gradedIndex
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) k) =
        ((univ : Finset (Fin (m + 2))), N + 2)) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A (N + 2), (I.attachment g).rows.IsLawful R ∧
      ∃ (gg : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        ∀ c : Fin (I.attachment g).card,
          (I.attachment g).toCellScheme.scope c ⊆ (I.replicated g H Γ A B').toCellScheme.scope k →
          (I.attachment g).toCellScheme.grade c ≤ N + 2 →
          min (w (I.attachEmb g H Γ A B' c)) (w k) =
            min (σ (R c)) (gg ((I.attachment g).toCellScheme.grade c)) := by
  obtain ⟨R, hRC, hR, hrowA, -⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard N m hN _ hko
  obtain ⟨gg, σ, hwit, hq⟩ := (Rows.isLawfulBelow_iff_forall.mp hw).2.1 k hk
  refine ⟨R, hRC, hR, gg, σ, hwit, fun c hcs hcg ↦ ?_⟩
  have hkg : (I.replicated g H Γ A B').toCellScheme.grade k = N + 2 :=
    congrArg Prod.snd hko
  have hmem : I.attachEmb g H Γ A B' c ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex k) := by
    rw [CellScheme.mem_below, gradedIndex_attachEmb]
    exact ⟨hcs, hcg.trans hkg.ge⟩
  have h := hq ⟨_, hmem⟩
  simp only at h
  rw [← Scheme.rowAt_of_mem hmem, Scheme.rowAt_mirror_of_mem hmem] at h
  have hgc : (I.replicated g H Γ A B').toCellScheme.grade (I.attachEmb g H Γ A B' c) =
      (I.attachment g).toCellScheme.grade c :=
    congrArg Prod.snd (gradedIndex_attachEmb c)
  rw [hgc] at h
  refine h.trans ?_
  congr 2
  change (I.attachTower g H Γ A B').rowAt _
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = R c
  rw [Scheme.mirrorOrig_castAdd]
  exact hrowA c hcg

end Seed

end VaughtConjecture

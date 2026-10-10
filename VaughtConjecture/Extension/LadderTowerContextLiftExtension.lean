/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftState

/-!
# The context lift through an extension over the tower

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

The single-writing coding of states (`Seed.StateCodingR`) asks the whole lift below `(univ, j)` to
be the decoded writing of one catalogue state.  It has a necessary condition
(`Seed.exists_member_of_stateCodingR`): an ambient separating the last two rungs of a member forces
a catalogue state with that member, since a writing reads the rungs of another member only up to
the cut of the two rank vectors.  The form is replaced here.

**The extension over the tower** (`Seed.TowerExtension j`): every complete lawful state of the
attachment satisfying `A (m + 2)`, with the observation at a cap `c` of an ambient `q` lawful below
`(univ, j)` on the cells of the attachment below the grade, extends to a labelling lawful below
`(univ, j)` that is the state at the cells of the attachment and keeps the observation of `q` at
`c` at every cell: on the ladder, the layers and the copies.  No single writing is asked: the
values on the ladder may come from the ambient's own member (the capped decoder of the ambient at a
top rung applied to the row of that rung, as in the lift at the grade one,
`Seed.cappedLift_mixed_univ_one`), and the values on the layers from the coded state.

* `Seed.towerExtension_of_stateCodingR`: the single-writing coding gives the extension (its decoded
  writing is one), so the extension is the weaker statement.
* `Seed.exists_towerExtension_top`: at the cap `⊤`, a state equal to the ambient on the attachment
  is extended by the ambient itself.  So the instance behind `Seed.exists_member_of_stateCodingR`
  forces nothing here: no member is asked of any catalogue state.
* **The reduction, re-run** (`Seed.cappedLift_context_of_towerExtension`,
  `Seed.hasContextLift_of_towerExtension`, `Seed.hasContextLift_attachAdmits_ext`): the context lift
  from the state lift (proved for the admission predicate given the ambient's admission,
  `Seed.contextStateLiftR_attachAdmits`) and the extension over the tower.

The extension over the tower, the context lift and a lawful labelling extending the labels of the
attachment (`Seed.HasExtendingLabel`) stay separate statements; nothing here gives the labelling.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (I g H Γ A B') in
/-- **The extension over the tower at the grade `j`**: every complete lawful state of the
attachment satisfying `A (m + 2)`, with the observation at a cap `c` self-visible at `j` of an
ambient `q` lawful below `(univ, j)` on the cells of the attachment below the grade, extends to a
labelling lawful below `(univ, j)`, equal to the state at the cells of the attachment and with the
observation of `q` at `c` at every cell below `(univ, j)`. -/
def TowerExtension (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (q : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
      A (m + 2) P →
      (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c) →
      ∃ q' : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j) → Label.{u},
        (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q' ∧
        (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
            ((univ : Finset (Fin (m + 2))), j)) a,
          I.attachEmb g H Γ A B' a = d.1 → q' d = P a) ∧
        ∀ d, min (q' d) c = min (q d) c

/-- **The single-writing coding gives the extension over the tower**: the decoded writing of the
coded state is lawful (through its companion), is the state at the cells of the attachment below
the grade, and keeps the observation of the ambient. -/
theorem towerExtension_of_stateCodingR (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j : ℕ}
    (hC : StateCodingR I g H Γ A B' j) : TowerExtension I g H Γ A B' j := by
  intro c hc q hq P hP hPA hPq
  obtain ⟨R, hR, ν, hν, ⟨r, hr, hbot⟩, hνR, hνq⟩ := hC c hc q hq P hP hPA hPq
  have hRl : (I.attachment g).rows.IsLawful R := (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  refine ⟨fun d ↦ ν (I.replicatedWriting g H Γ A B' R d),
    ((isLawful_replicatedWriting hH hcard hΓ hA hR).isLawfulBelow _).map_of_bot_iff hr
      (fun d ↦ d.2.2) hν hbot, fun d a ha ↦ ?_, hνq⟩
  have hag : (I.attachment g).toCellScheme.grade a ≤ j :=
    ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a
      ((univ : Finset (Fin (m + 2))), j)).mp (ha ▸ d.2)).2
  change ν (I.replicatedWriting g H Γ A B' R d.1) = P a
  rw [← ha, replicatedWriting_attachEmb hcard hRl, hνR a hag]

/-- **At the cap `⊤` the ambient is an extension** of a state equal to it on the attachment: no
member is forced, unlike the single-writing coding (`Seed.exists_member_of_stateCodingR`). -/
theorem exists_towerExtension_top {j : ℕ}
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q)
    {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ (d : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a, I.attachEmb g H Γ A B' a = d.1 → P a = q d) :
    ∃ q' : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u},
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q' ∧
      (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.attachEmb g H Γ A B' a = d.1 → q' d = P a) ∧
      ∀ d, min (q' d) ⊤ = min (q d) ⊤ :=
  ⟨q, hq, fun d a ha ↦ (hPq d a ha).symm, fun _ ↦ rfl⟩

/-- **The context lift at the grade `j` from the state lift and the extension over the tower**:
the extension of the lifted state is lawful below `(univ, j)`, reads the prescription on the
context cells, and keeps the observation of the ambient at the cap. -/
theorem cappedLift_context_of_towerExtension {j : ℕ} (hS : ContextStateLiftR I g H Γ A B' j)
    (hE : TowerExtension I g H Γ A B' j) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨P, hPl, hPA, hPp, hPq⟩ := hS c hc p q hp hq hpq
  obtain ⟨q', hq', hq'P, hq'q⟩ := hE c hc q hq P hPl hPA hPq
  refine ⟨q', hq', hq'q, fun d ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx d.2
  exact (hq'P _ a ha).trans (hPp d a ha)

/-- **The context lift from the state lift and the extension over the tower** at every grade
`1, …, m + 1`. -/
theorem hasContextLift_of_towerExtension
    (h : ∀ j, 1 ≤ j → j ≤ m + 1 →
      ContextStateLiftR I g H Γ A B' j ∧ TowerExtension I g H Γ A B' j) :
    I.HasContextLift g H Γ A B' := fun j hj hjm ↦
  cappedLift_context_of_towerExtension (h j hj hjm).1 (h j hj hjm).2

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The context lift of the replicated scheme from the ambient's admission and the extension
over the tower**, for requests calibrated on the class with the labels pair admitted and the
relative lift on the exact class over a legal donor with a nonempty root: the state lift
(`Seed.contextStateLiftR_attachAdmits`) and the extension at every grade. -/
theorem hasContextLift_attachAdmits_ext
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hamb : ∀ j, 1 ≤ j → j ≤ m + 1 → AmbientAdmitted I g H Γ B' hd Q j)
    (hE : ∀ j, 1 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_of_towerExtension fun j hj hjm ↦
    ⟨contextStateLiftR_attachAdmits hte hdp hdL hn hd hQ hpair hrel hj (hamb j hj hjm),
      hE j hj hjm⟩

end Seed

end VaughtConjecture

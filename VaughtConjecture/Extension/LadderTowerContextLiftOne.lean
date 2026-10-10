/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftAmbient

/-!
# The context lift at the grade one

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

At the grade one the context lift of the replicated scheme holds outright
(`Seed.cappedLift_context_one`), from the lemmas of the grade one: the attachment lifts capped from
the context face into `(univ, 1)` (`Seed.cappedLift_attachment_univ_one`, the lifts of the amalgam
within the context face and the donor face glued along the root), the tower does so by gluing of
rank members (`Seed.cappedLift_attachTower_one`), and the replicated scheme does so from the tower
(`Seed.cappedLift_replicated_of_tower`).  The hypotheses on the donor face and the root are those
of `Seed.cappedLift_attachment_univ_one`.

So the context lift needs the extension over the tower only at the grades `2, …, m + 1`
(`Seed.hasContextLift_attachAdmits_two`).  `Seed.hasContextLift_attachAdmits_tower` is unchanged.

**The state at most the cap** (`Seed.towerExtension_of_le`): when the state does not exceed the cap
at the cells of the attachment below the grade, the ambient capped at the cap is an extension.  So
the extension is asked only above the cap (`Seed.TowerExtensionAbove`,
`Seed.towerExtension_of_above`): where the state exceeds the cap, some cell of full scope at each
grade must carry the new values, and its row must read them.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The context lift at the grade one**, when the donor face and the root (its intersection
with the context face) are faces of the amalgam and the root is nonempty. -/
theorem cappedLift_context_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  set C := univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) with hC
  have hCF : C ∈ I.amalgam.toCellScheme.faces :=
    ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hC1 : 1 ≤ #C := by rw [hC, card_map, card_univ, Fintype.card_fin]; omega
  have hXU : ((C, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨subset_univ _, le_rfl⟩
  have hX : ¬ (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤ (C, 1) :=
    fun h ↦ map_castSuccEmb_ne_univ (univ_subset_iff.mp h.1)
  have hl : (I.replicated g H Γ A B').rows.CappedLift hXU :=
    cappedLift_replicated_of_tower hXU rfl (.inl subset_rfl)
      (cappedLift_attachTower_one hH hcard hXU hX
        (cappedLift_attachment_univ_one hdF hrF hr1 hCF hC1 (.inl subset_rfl)))
  have key : ∀ (D : Finset (Fin (m + 2)))
      (h : ((D, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1)),
      D = C → (I.replicated g H Γ A B').rows.CappedLift h := by
    rintro D h rfl
    exact hl
  exact key _ _ map_castSuccEmb_eq_ctxCoatom.symm

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The context lift of the replicated scheme from the extension over the tower at the grades
`2, …, m + 1`**: at the grade one the lift holds outright (`Seed.cappedLift_context_one`), above it
by the state lift and the extension (`Seed.cappedLift_context_of_towerExtension`). -/
theorem hasContextLift_attachAdmits_two (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hE : ∀ j, 2 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' := by
  intro j hj hjm
  rcases Nat.lt_or_ge j 2 with h1 | h2
  · obtain rfl : j = 1 := by omega
    exact cappedLift_context_one hH hcard ((restrictFace_eq_some_iff _ _).mp hd).1 hrF hr1
  · exact cappedLift_context_of_towerExtension
      (contextStateLiftR_attachAdmits hte hdp hdL hn hd hQ hpair hrel hj
        (ambientAdmitted hH hcard hΓ0 hd hQ hn j)) (hE j h2 hjm)

/-! ### The extension over the tower when the state stays below the cap -/

/-- **The extension over the tower when the state stays at most the cap**: if the state is at most
the cap `c` at the cells of the attachment below the grade, the ambient capped at `c` is an
extension (capping at a label self-visible at the grade keeps lawfulness,
`CellScheme.Rows.IsLawfulBelow.min_const_of_isSelfVisible`).  At the cap `⊤` this is every input. -/
theorem towerExtension_of_le {j : ℕ} {c : Label.{u}} (hc : IsSelfVisible j c)
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q)
    {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ (d : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a,
      I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c)
    (hle : ∀ a, (I.attachment g).toCellScheme.grade a ≤ j → P a ≤ c) :
    ∃ q' : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u},
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q' ∧
      (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.attachEmb g H Γ A B' a = d.1 → q' d = P a) ∧
      ∀ d, min (q' d) c = min (q d) c := by
  refine ⟨fun d ↦ min (q d) c, hq.min_const_of_isSelfVisible hc, fun d a ha ↦ ?_,
    fun d ↦ by rw [min_assoc, min_self]⟩
  have hag : (I.attachment g).toCellScheme.grade a ≤ j :=
    ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a
      ((univ : Finset (Fin (m + 2))), j)).mp (ha ▸ d.2)).2
  exact (hPq d a ha).symm.trans (min_eq_left (hle a hag))

variable (I g H Γ A B') in
/-- **The extension over the tower above the cap at the grade `j`**: `Seed.TowerExtension j` asked
only of the inputs whose state exceeds the cap at some cell of the attachment below the grade. -/
def TowerExtensionAbove (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (q : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
      A (m + 2) P →
      (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c) →
      (∃ a, (I.attachment g).toCellScheme.grade a ≤ j ∧ ¬ P a ≤ c) →
      ∃ q' : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j) → Label.{u},
        (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q' ∧
        (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
            ((univ : Finset (Fin (m + 2))), j)) a,
          I.attachEmb g H Γ A B' a = d.1 → q' d = P a) ∧
        ∀ d, min (q' d) c = min (q d) c

/-- **The extension over the tower from its case above the cap**
(`Seed.towerExtension_of_le` for the other inputs). -/
theorem towerExtension_of_above {j : ℕ} (h : TowerExtensionAbove I g H Γ A B' j) :
    TowerExtension I g H Γ A B' j := by
  intro c hc q hq P hP hPA hPq
  by_cases hhigh : ∃ a, (I.attachment g).toCellScheme.grade a ≤ j ∧ ¬ P a ≤ c
  · exact h c hc q hq P hP hPA hPq hhigh
  · push Not at hhigh
    exact towerExtension_of_le hc hq hPq hhigh

/-- **The context lift of the replicated scheme from the extension above the cap at the grades
`2, …, m + 1`** (`Seed.hasContextLift_attachAdmits_two`, `Seed.towerExtension_of_above`). -/
theorem hasContextLift_attachAdmits_above (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hE : ∀ j, 2 ≤ j → j ≤ m + 1 → TowerExtensionAbove I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_attachAdmits_two hH hcard hΓ0 hte hdp hdL hn hd hQ hpair hrel hrF hr1
    fun j hj hjm ↦ towerExtension_of_above (hE j hj hjm)

end Seed

end VaughtConjecture

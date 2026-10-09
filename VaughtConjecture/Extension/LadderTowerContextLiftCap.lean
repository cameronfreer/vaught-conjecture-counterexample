/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftOne
import VaughtConjecture.Extension.ReplicatedStateCoding

/-!
# The extension over the tower at the cap `⊥`

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

At the cap `⊥` the extension over the tower (`Seed.TowerExtension`) asks only a lawful labelling
below `(univ, j)` equal to the state at the cells of the attachment.  For the admission predicate
and a set of values containing the code set of the attachment (`Label.codeSet`), the state is the
reading of a catalogue state `R` by a witness `σ` sending only `⊥` to `⊥`
(`Seed.exists_stateCode`), and the decoded writing `σ ∘ replicatedWriting R` is such a labelling
(`Seed.isLawfulBelow_map_replicatedWriting`, `Seed.replicatedWriting_attachEmb`).

So the extension is asked only at a positive cap where the state exceeds the cap
(`Seed.TowerExtensionPos`, `Seed.towerExtension_of_pos`; the state at most the cap is
`Seed.towerExtension_of_le`), and the context lift follows from that case at the grades
`2, …, m + 1` (`Seed.hasContextLift_attachAdmits_pos`).

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (I g H Γ A B') in
/-- **The extension over the tower at a positive cap above the state's bound** at the grade `j`:
`Seed.TowerExtension j` asked only at caps other than `⊥` and of the inputs whose state exceeds the
cap at some cell of the attachment below the grade. -/
def TowerExtensionPos (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c → c ≠ ⊥ →
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

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The extension over the tower from its case at a positive cap above the state's bound**: at
the cap `⊥` the decoded writing of the code of the state is an extension; a state at most the cap
is extended by the ambient capped (`Seed.towerExtension_of_le`). -/
theorem towerExtension_of_pos (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ) {j : ℕ} (hj : j ≤ m + 2)
    (h : TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j) :
    TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j := by
  refine towerExtension_of_above fun c hc q hq P hP hPA hPq hhigh ↦ ?_
  by_cases hc0 : c = ⊥
  · subst hc0
    obtain ⟨R, hR, σ, hσ, hbot, hσR⟩ := exists_stateCode hd hQ hΓc hP hPA
    have hRl : (I.attachment g).rows.IsLawful R := (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
    refine ⟨fun d ↦ σ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' R d),
      isLawfulBelow_map_replicatedWriting hH hcard hΓ
        (fun k R h ↦ I.attachAdmits_succ g hd Q k R h) hR _ (hσ j hj) hbot,
      fun d a ha ↦ ?_, fun d ↦ by rw [min_bot_right, min_bot_right]⟩
    change σ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' R d.1) = P a
    rw [← ha]
    exact (congrArg σ (replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q)
      (B' := B') hcard hRl a)).trans (hσR a)
  · exact h c hc hc0 q hq P hP hPA hPq hhigh

/-- **The context lift of the replicated scheme from the extension at a positive cap above the
state's bound at the grades `2, …, m + 1`**, for a set of values containing the code set of the
attachment. -/
theorem hasContextLift_attachAdmits_pos (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hE : ∀ j, 2 ≤ j → j ≤ m + 1 → TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_attachAdmits_two hH hcard hΓ0 hte hdp hdL hn hd hQ hpair hrel hrF hr1
    fun j hj hjm ↦ towerExtension_of_pos hH hcard hΓ hd hQ hΓc (by omega) (hE j hj hjm)

end Seed

end VaughtConjecture

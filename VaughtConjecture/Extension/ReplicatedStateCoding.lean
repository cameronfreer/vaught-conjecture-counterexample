/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.FinitePartSquash
import VaughtConjecture.MainTheorem.ReplicatedCompletion

/-!
# The coding of states of the attachment by the catalogue

Roadmap, Layer 3 ((R3) and (R4), the coding of states in the extension over the tower).

**The coding of states at a grade `j`** (`Seed.StateCodingAt j`): every complete lawful state `P`
of the attachment satisfying `A (m + 2)` is read, at the cells of grade at most `j`, from a state
`R` of the catalogue at the grade `m + 2` by a witness bounded by `j`.

**The block compression alone needs the values to grow with the state**: it keeps the finite part
of every label (`Label.blockCompress_coe`), so a set of values containing the compressed values of
`P` bounds the finite parts of the values of `P` (`Label.finNat_le_of_blockCompress_mem`).  The
values `Γ` are fixed once for the whole assembly, so the block compression alone codes only the
states whose finite parts are bounded in advance.  The finite parts above the grade `m + 2` are
invisible to the reads and to the laws, so they are renumbered first (`Label.squash`, a witness
bounded by `m + 2` inverted on the values of `P` by `Label.unsquash`); the code set then bounds
the values of every code, whatever the state (`Label.le_gridPoint_of_mem_codeSet`,
`Label.lt_omega0_sq_of_mem_codeSet`).

**The coding** (`Seed.stateCoding_attachAdmits`): for requests calibrated on the class, and every
set `Γ` containing the code set `Label.codeSet |cells| (m + 2)` (fixed by the seed:
`⊥` and `ω * i + f` with `i ≤ |cells|`, `f < 3 (m + 2) + |cells| + 3`), the state
`R = blockCompress ∘ squash ∘ P` is in the catalogue: its values lie in the code set
(`Label.blockCompress_squash_mem_codeSet`), it is lawful (a witness reflecting `⊥` on the values of
`P`), and it is admitted (the requests are carried by the witness,
`StageType.GrowthRequests.CorrectAt.map`); the witness `unsquash ∘ blockExpand`, bounded by every
grade up to `m + 2`, reads `R` as `P` at every cell (`Seed.exists_stateCode`).  The capped form
reads `R` as `P` capped at a label self-visible at `j` (`Seed.exists_stateCode_capped`).

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Witnesses are [Kni26, Definition 2.3.9]; visibility replacement is [Kni26, Definition 2.2.3]; the
growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Label

/-- **The block compression keeps the finite parts**: a set of values containing the block
compression of an ordinal label of `V` bounds its finite part. -/
theorem finNat_le_of_blockCompress_mem {V Γ : Finset Label.{u}} {K : ℕ} {a : Ordinal.{u}}
    (ha : (a : Label.{u}) ∈ V) (hΓ : blockCompress V K a ∈ Γ) :
    finNat a ≤ Γ.sup labelFinNat := by
  have h := Finset.le_sup (f := labelFinNat) hΓ
  rwa [blockCompress_coe ha, labelFinNat_coe,
    finNat_add_natCast (isSuccPrelimit_omega0_mul _)] at h

/-- The code set lies below the grid point `ω * B' + 2` once `C < B'`. -/
theorem le_gridPoint_of_mem_codeSet {C K B' : ℕ} (hB : C + 1 ≤ B') {x : Label.{u}}
    (hx : x ∈ codeSet C K) : x ≤ gridPoint 2 B' := by
  rcases mem_insert.mp hx with rfl | hx
  · exact bot_le
  obtain ⟨⟨i, f⟩, hp, rfl⟩ := mem_image.mp hx
  have hi : i < B' := by have := mem_range.mp (mem_product.mp hp).1; omega
  rw [gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
  have h1 : Ordinal.omega0 * (i : Ordinal.{u}) + f <
      Ordinal.omega0 * ((i + 1 : ℕ) : Ordinal.{u}) := by
    rw [Nat.cast_succ, mul_add_one]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 _) _
  exact (h1.le.trans (omega0_mul_natCast_le_iff.mpr hi)).trans le_self_add

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

variable (I g) in
/-- **The coding of states at the grade `j`**: every complete lawful state `P` of the attachment
satisfying `A (m + 2)` is read at the cells of grade at most `j` from a state `R` of the catalogue
at the grade `m + 2` by a witness bounded by `j`. -/
def StateCodingAt (Γ : Finset Label.{u})
    (A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop) (j : ℕ) : Prop :=
  ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P → A (m + 2) P →
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2), ∃ σ : Label.{u} → Label.{u},
      IsWitness (stepSuppressor j) σ ∧
        ∀ a, (I.attachment g).toCellScheme.grade a ≤ j → σ (R a) = P a

variable {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **Admission is carried by a witness** bounded by `m + 2` and sending only `⊥` to `⊥` on the
values of the state, for requests calibrated on the class. -/
theorem attachAdmits_comp {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {P : Fin (I.attachment g).card → Label.{u}} (hPA : I.attachAdmits g hd Q (m + 2) P)
    {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor (m + 2)) ν)
    (hbot : ∀ a, ν (P a) = ⊥ ↔ P a = ⊥) (K : ℕ) : I.attachAdmits g hd Q K (ν ∘ P) := by
  intro _ hcls hcap j
  have hthr : Q.threshold ≤ m + 2 := (I.left.grade_le Q.cap).trans (Nat.le_succ _)
  have hhat (a : Fin (I.attachment g).card) :
      I.attachHatAt g Q.threshold (ν ∘ P) a = ν (I.attachHatAt g Q.threshold P a) :=
    attachHatAt_comp hν.map_bot _ P a
  have hhbot (a : Fin (I.attachment g).card) :
      ν (I.attachHatAt g Q.threshold P a) = ⊥ ↔ I.attachHatAt g Q.threshold P a = ⊥ := by
    unfold attachHatAt
    split_ifs
    · exact hbot a
    · exact ⟨fun _ ↦ rfl, fun _ ↦ hν.map_bot⟩
  have hP := hPA hthr (fun x hx ↦ by
      have h := hcls x hx
      simp only [hhat] at h
      exact (hhbot _).symm.trans h)
    (fun h0 ↦ hcap (by
      simp only [hhat]
      exact (hhbot _).mpr h0)) j
  have hθv : ∀ i ≤ Q.threshold, ∀ x, ν (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (ν x) := fun i hi x ↦
    hν.visibilityReplace_comm x _ (by rw [stepSuppressor_of_le hthr]; exact le_top) i hi
  have hmap := hP.map hν.monotone hν.map_bot hθv (fun hf ↦ (hQ.ref j hf).2.1) hQ.marker.2.1
  have e1 : (fun x ↦ I.attachHatAt g Q.threshold (ν ∘ P) (I.attachCtxCell g x)) =
      ν ∘ fun x ↦ I.attachHatAt g Q.threshold P (I.attachCtxCell g x) := funext fun x ↦ hhat _
  change Q.CorrectAt (fun x ↦ I.attachHatAt g Q.threshold (ν ∘ P) (I.attachCtxCell g x)) j
    (I.attachHatAt g Q.threshold (ν ∘ P) (I.attachDonCell g hd j))
  rw [e1, hhat]
  exact hmap

/-- **The code of a state**: for requests calibrated on the class and values containing the code
set of the attachment at `m + 2`, every complete lawful admitted state `P` of the attachment is
read from a state `R` of the catalogue at `m + 2` by a witness `σ` bounded by every grade up to
`m + 2`, sending only `⊥` to `⊥`, at every cell. -/
theorem exists_stateCode {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {Γ : Finset Label.{u}}
    (hΓ : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : I.attachAdmits g hd Q (m + 2) P) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2),
      ∃ σ : Label.{u} → Label.{u}, (∀ j ≤ m + 2, IsWitness (stepSuppressor j) σ) ∧
        (∀ x, σ x = ⊥ → x = ⊥) ∧ ∀ a, σ (R a) = P a := by
  classical
  set V : Finset Label.{u} := univ.image P with hV
  set W : Finset Label.{u} := V.image (squash V (m + 2)) with hW
  have hPV (a : Fin (I.attachment g).card) : P a ∈ V := mem_image_of_mem _ (mem_univ a)
  have hPW (a : Fin (I.attachment g).card) : squash V (m + 2) (P a) ∈ W :=
    mem_image_of_mem _ (hPV a)
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  -- the squashed state
  set S : Fin (I.attachment g).card → Label.{u} := squash V (m + 2) ∘ P with hSdef
  have hSl : (I.attachment g).rows.IsLawful S :=
    hP.map_of_bot_iff hP hgr isWitness_squash fun a ↦ squash_eq_bot_iff
  have hSA : I.attachAdmits g hd Q (m + 2) S :=
    attachAdmits_comp hd hQ hPA isWitness_squash (fun a ↦ squash_eq_bot_iff) _
  -- the compressed state
  set R : Fin (I.attachment g).card → Label.{u} := blockCompress W (m + 2) ∘ S with hRdef
  have hRl : (I.attachment g).rows.IsLawful R :=
    hSl.map_of_bot_iff hSl hgr (isWitness_blockCompress (m + 2))
      fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)
  have hRA : I.attachAdmits g hd Q (m + 2) R :=
    attachAdmits_comp hd hQ hSA (isWitness_blockCompress (m + 2))
      (fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)) _
  have hVc : #V ≤ (I.attachment g).card := card_image_le.trans (by simp)
  refine ⟨R, Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ hΓ
      (blockCompress_squash_mem_codeSet hVc (hPV a)), hRl, hRA⟩,
    unsquash V (m + 2) ∘ blockExpand W, fun j hj ↦ ?_, fun x hx ↦ ?_, fun a ↦ ?_⟩
  · exact IsWitness.comp_of_bot_reflecting (isWitness_blockExpand j)
      (isWitness_unsquash.of_le_stepSuppressor hj) fun x hx ↦ unsquash_eq_bot_iff.mp hx
  · exact blockExpand_eq_bot_iff.mp (unsquash_eq_bot_iff.mp hx)
  · change unsquash V (m + 2) (blockExpand W (blockCompress W (m + 2)
      (squash V (m + 2) (P a)))) = P a
    rw [blockExpand_blockCompress (hPW a), unsquash_squash (hPV a)]

/-- **The coding of states holds at every grade** for the admission predicate of requests
calibrated on the class, once the values contain the code set of the attachment at `m + 2`. -/
theorem stateCoding_attachAdmits {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {Γ : Finset Label.{u}}
    (hΓ : codeSet (I.attachment g).card (m + 2) ⊆ Γ) {j : ℕ} (hj : j ≤ m + 2) :
    StateCodingAt I g Γ (I.attachAdmits g hd Q) j := by
  intro P hP hPA
  obtain ⟨R, hR, σ, hσ, -, hσR⟩ := exists_stateCode hd hQ hΓ hP hPA
  exact ⟨R, hR, σ, hσ j hj, fun a _ ↦ hσR a⟩

/-- **The capped form**: for a label `x` self-visible at `j`, the state of the code is read as `P`
capped at `x` at the cells of grade at most `j`, by the code witness under the cap. -/
theorem exists_stateCode_capped {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {Γ : Finset Label.{u}}
    (hΓ : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : I.attachAdmits g hd Q (m + 2) P) {j : ℕ} (hj : j ≤ m + 2) {x : Label.{u}}
    (hx : IsSelfVisible j x) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2),
      ∃ (gg : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        ∀ a, (I.attachment g).toCellScheme.grade a ≤ j →
          min (σ (R a)) (gg ((I.attachment g).toCellScheme.grade a)) = min (P a) x := by
  obtain ⟨R, hR, σ, hσ, -, hσR⟩ := exists_stateCode hd hQ hΓ hP hPA
  refine ⟨R, hR, _, σ, (hσ j hj).cap hx, fun a ha ↦ ?_⟩
  simp only [ite_eq_left ha, stepSuppressor_of_le ha, min_top_left, hσR a]

end Seed

end VaughtConjecture

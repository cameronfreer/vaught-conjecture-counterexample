/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderMembers
import VaughtConjecture.Extension.SeedAttachment
import VaughtConjecture.Label.FinitePartSquash

/-!
# Rank agreement of a coded state with the ambient's member pins its values

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap).

For the extension over the tower at a cap `⊥ < c < ⊤` the serving cell of a grade is the layer
cell of the code `R` of a state `P'` equal to the prescription `P` below the grade `j`
(`Seed.exists_stateCode`).  Its row reads the ladder through the rank member of `R`, so the
observation of the ambient on the ladder asks the rank vector of `R` to agree with the ambient's
ladder member `b` below the first rank `k` where the table of `b` reaches the cap
(`Label.RankAgree (rankVector R) b k`, through `Scheme.baseIndex_agree`).

**Rank agreement pins values across grades.**  Two cells with the same rank in `b` below `k` have
the same rank in `R` (`Label.rankVector_eq_of_rankAgree`), hence the same value of `R`
(`Label.eq_of_rankVector_eq`), hence the same value of every state read from `R`
(`Seed.eq_of_coded_rankAgree`).  A lawful state carries at every cell a label self-visible at its
grade, so the value at a cell of grade at most `j` must be self-visible at the grade of every cell
of the same rank in `b` below `k`, whatever the grades above `j` are given
(`Seed.isSelfVisible_of_coded_rankAgree`).

**The failing statement** (`Seed.not_exists_coded_rankAgree`): if a cell `d₁` of grade at most `j`
and a cell `d₂` have the same rank in `b`, below `k`, and the prescribed value `P d₁` is not
self-visible at the grade of `d₂`, then no lawful state `P'` equal to `P` below the grade, read
from any `R` by any map, has the rank vector of `R` agreeing with `b` below `k`.  The freedom above
the grade does not help: the value at `d₂` is pinned to `P d₁`.  The hypotheses on the ambient
(lawful below `(univ, j)`, with `P` equal to it capped at `c` below the grade) bound the
visibility of `P d₁` only at the grades up to `j`: the ambient's controllers read the attachment
through decoders that are witnesses bounded by `j`.  The collapse of the finite parts at `j`
(`Label.finCollapse`), a witness bounded by `j` (`Label.isWitness_finCollapse`), lowers every
finite part above `j` to `j`: it
keeps an ambient lawful below a pair of grade `j` and makes its values self-visible at no grade
above `j` (`Label.not_isSelfVisible_finCollapse`).  A complete instance (a seed, an ambient, its
member with two cells of one rank across the grade, and an admitted prescription) is not compiled
here.

**Scope.**  An obstruction to the earlier constructions (the replicated scheme over the height-set
tower, or carriers with admitted controllers), or a step of one; not used by the main theorem
through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept as the compiled
reason that construction was replaced.

## References

Lawful sections are [Kni26, Definition 2.5.4]; visibility replacement is
[Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {ι : Type*} [Fintype ι] {R : ι → Label.{u}}

/-- **Equal ranks are equal values.** -/
theorem eq_of_rankVector_eq {d₁ d₂ : ι} (h : rankVector R d₁ = rankVector R d₂) :
    R d₁ = R d₂ :=
  le_antisymm (le_of_valueRank_le h.le) (le_of_valueRank_le h.ge)

/-- **Below the agreement height the rank is the other vector's rank.** -/
theorem rankVector_eq_of_rankAgree {b : ι → ℕ} {k : ℕ} (h : RankAgree (rankVector R) b k)
    {d : ι} (hd : b d < k) : rankVector R d = b d := by
  have e := h d
  rw [min_eq_left hd.le] at e
  rcases le_total (rankVector R d) k with hle | hle
  · rwa [min_eq_left hle] at e
  · rw [min_eq_right hle] at e
    omega

/-- **The collapse of the finite parts at `j`**: the finite parts above `j` are lowered to `j`. -/
noncomputable def finCollapse (j : ℕ) : Label.{u} → Label.{u} := blockwise fun f ↦ min f j

/-- **The collapse at `j` is a witness bounded by `j`**: an ambient lawful below a pair of grade
`j`, collapsed, stays lawful, since it sends only `⊥` to `⊥`
(`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`). -/
theorem isWitness_finCollapse (j : ℕ) : IsWitness (stepSuppressor j) (finCollapse.{u} j) :=
  isWitness_blockwise (fun _ _ h ↦ min_le_min_right j h) fun _ hf ↦ min_eq_left hf

theorem finCollapse_eq_bot_iff (j : ℕ) {x : Label.{u}} : finCollapse j x = ⊥ ↔ x = ⊥ :=
  blockwise_eq_bot_iff _

/-- **A collapsed label of finite part at least `j` is self-visible at no grade above `j`.** -/
theorem not_isSelfVisible_finCollapse {j : ℕ} {a : Ordinal.{u}} (ha : j ≤ finNat a) {k : ℕ}
    (hk : j < k) : ¬ IsSelfVisible k (finCollapse j (a : Label.{u})) := by
  rw [finCollapse, blockwise_coe, isSelfVisible_coe, finNat_spec,
    finNat_add_natCast (isSuccPrelimit_blockOf a), min_eq_right ha]
  exact_mod_cast not_le.mpr hk

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-- **Rank agreement pins the values of a coded state**: if the rank vector of `R` agrees with `b`
below `k`, two cells of the same rank in `b` below `k` carry the same value of every state read
from `R`. -/
theorem eq_of_coded_rankAgree {R P' : Fin (I.attachment g).card → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hσ : ∀ a, σ (R a) = P' a)
    {b : Fin (I.attachment g).card → ℕ} {k : ℕ} (hag : RankAgree (rankVector R) b k)
    {d₁ d₂ : Fin (I.attachment g).card} (hb : b d₁ = b d₂) (hk : b d₂ < k) : P' d₁ = P' d₂ := by
  have h1 := rankVector_eq_of_rankAgree hag (hb ▸ hk)
  have h2 := rankVector_eq_of_rankAgree hag hk
  rw [← hσ, ← hσ, eq_of_rankVector_eq (h1.trans (hb.trans h2.symm))]

/-- **A lawful coded state carries at a cell a label self-visible at the grade of every cell of
the same rank in `b` below `k`.** -/
theorem isSelfVisible_of_coded_rankAgree {R P' : Fin (I.attachment g).card → Label.{u}}
    (hP' : (I.attachment g).rows.IsLawful P') {σ : Label.{u} → Label.{u}}
    (hσ : ∀ a, σ (R a) = P' a) {b : Fin (I.attachment g).card → ℕ} {k : ℕ}
    (hag : RankAgree (rankVector R) b k) {d₁ d₂ : Fin (I.attachment g).card}
    (hb : b d₁ = b d₂) (hk : b d₂ < k) :
    IsSelfVisible ((I.attachment g).toCellScheme.grade d₂) (P' d₁) :=
  eq_of_coded_rankAgree hσ hag hb hk ▸ hP'.orderly d₂

/-- **The failing statement**: if a cell `d₁` of grade at most `j` and a cell `d₂` have the same
rank in `b`, below `k`, and the prescribed value `P d₁` is not self-visible at the grade of `d₂`,
then no lawful state equal to `P` at the cells of grade at most `j`, read from any `R` by any map,
has the rank vector of `R` agreeing with `b` below `k`. -/
theorem not_exists_coded_rankAgree {P : Fin (I.attachment g).card → Label.{u}} {j : ℕ}
    {b : Fin (I.attachment g).card → ℕ} {k : ℕ} {d₁ d₂ : Fin (I.attachment g).card}
    (hd₁ : (I.attachment g).toCellScheme.grade d₁ ≤ j) (hb : b d₁ = b d₂) (hk : b d₂ < k)
    (hvis : ¬ IsSelfVisible ((I.attachment g).toCellScheme.grade d₂) (P d₁)) :
    ¬ ∃ (P' R : Fin (I.attachment g).card → Label.{u}) (σ : Label.{u} → Label.{u}),
      (I.attachment g).rows.IsLawful P' ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → P' a = P a) ∧
        (∀ a, σ (R a) = P' a) ∧ RankAgree (rankVector R) b k := by
  rintro ⟨P', R, σ, hP', hPP, hσ, hag⟩
  exact hvis (hPP d₁ hd₁ ▸ isSelfVisible_of_coded_rankAgree hP' hσ hag hb hk)

/-- The same for the rank vector of the state itself (`R = P'`, `σ = id`). -/
theorem not_exists_rankAgree {P : Fin (I.attachment g).card → Label.{u}} {j : ℕ}
    {b : Fin (I.attachment g).card → ℕ} {k : ℕ} {d₁ d₂ : Fin (I.attachment g).card}
    (hd₁ : (I.attachment g).toCellScheme.grade d₁ ≤ j) (hb : b d₁ = b d₂) (hk : b d₂ < k)
    (hvis : ¬ IsSelfVisible ((I.attachment g).toCellScheme.grade d₂) (P d₁)) :
    ¬ ∃ P' : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P' ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → P' a = P a) ∧
        RankAgree (rankVector P') b k := fun ⟨P', hP', hPP, hag⟩ ↦
  not_exists_coded_rankAgree hd₁ hb hk hvis ⟨P', P', id, hP', hPP, fun _ ↦ rfl, hag⟩

end Seed

end VaughtConjecture

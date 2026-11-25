/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderMembers
import VaughtConjecture.ProcessRank.SpanStateLift

/-!
# The restricted rank catalogue at the grade one and its one-sided rank glue

Process rank `ω₁`, the finite span of mutual rigidity: the grade-one layer of the master.

**The restricted catalogue** (`ProcessRank.IsSpanRankMember`).  For a scheme `S` (the common
scheme of the two types), a height `H`, a set `T` of cells and a threshold grade `K`, a rank vector
`a` on the fields `Fin S.card ⊕ Fin S.card` is a member when its ranks are at most `H` and dense,
both of its sides have lawful tables (`Scheme.HasLawfulTables`: every positive table read at the
ranks of the cells of grade one, `⊥` above, is lawful on `S`), and it is admitted at the grade one
on its ranks (`ProcessRank.IsAdmitted`, a condition only when `K = 1`).  The ranks cover every
field, those of grade above one included.  A **positive table** (`ProcessRank.IsPositiveTable`) is
monotone, `⊥` exactly at the rank `0` up to `H`, and self-visible at the grade one.

**The one-sided rank glue** (`ProcessRank.RestrictedRankGlueTarget`).  Let `a` be a member, `F` a
positive table, `c` a cap self-visible at the grade one, `ℓ` the first rank up to `H` at which `F`
reaches `c` (`H + 1` if none), and `r` lawful below a graded face `X` of grade one of `S`, agreeing
capped at `c` with the side `b` of the state `F ∘ a`.  Then some member `a'` and positive table
`F'` keep every rank below `ℓ` (`min (a x) ℓ = min (a' x) ℓ`) and the table below `ℓ`, agree with
`F` capped at `c` up to `H`, give a state agreeing with `F ∘ a` capped at `c` at every field, and
read `r` literally on the side `b` below `X`.  The other side and the new ranks are chosen
together; the unrestricted ladder glue `Scheme.RankGlue`, which takes a separately chosen
labelling of all cells, is not used, since it can break the admission.  The intended proof follows
the three cases of the state lift, with the comparisons of `m(a)`, `s(a)` and `ℓ` made on the
natural ranks: low ranks are kept exactly (also where table values repeat), new high values are
ranked densely from `ℓ`, and lawful tables come from `Scheme.hasLawfulTables_of_order`.  If no
field reaches `c` the member and the table are kept.

Only the statement is given here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label

variable {n : ℕ}

/-- A **member of the restricted rank catalogue**: ranks at most `H`, dense, lawful tables on both
sides, and admitted at the grade one on the ranks. -/
def IsSpanRankMember (S : Scheme.{u} n) (H : ℕ) (T : Set (Fin S.card)) (K : ℕ)
    (a : Fin S.card ⊕ Fin S.card → ℕ) : Prop :=
  (∀ x, a x ≤ H) ∧ (∀ i, 0 < i → ∀ x, i ≤ a x → ∃ y, a y = i) ∧
    (∀ b : Bool, Scheme.HasLawfulTables.{u} S H fun d ↦ a (sideField b d)) ∧ IsAdmitted T K 1 a

/-- A **positive table** up to `H`: monotone, `⊥` at `0`, self-visible at the grade one, and not
`⊥` at the positive ranks up to `H`. -/
def IsPositiveTable (H : ℕ) (F : ℕ → Label.{u}) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ i, IsSelfVisible 1 (F i)) ∧ ∀ i, 0 < i → i ≤ H → F i ≠ ⊥

/-- **Target: the one-sided rank glue in the restricted catalogue.**  For a legal scheme, a set
`T` of cells of grade at most `K`, a height `H ≥ 2 · |S|`, a member `a`, a positive table `F`, a
cap `c` self-visible at the grade one with first rank `ℓ` reaching it, and a labelling `r` lawful
below a graded face of grade one agreeing capped at `c` with the side `b` of `F ∘ a`, some member
`a'` and positive table `F'` keep the ranks and the table below `ℓ`, agree with `F` capped at `c`
up to `H` and with `F ∘ a` capped at `c` at every field, and read `r` on the side `b`.  Proved
(`ProcessRank.restrictedRankGlue`). -/
def RestrictedRankGlueTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Scheme.{u} n), S.IsLegal → ∀ (T : Set (Fin S.card)) (K H : ℕ),
    (∀ d ∈ T, S.toCellScheme.grade d ≤ K) → 2 * S.card ≤ H → 0 < H →
    ∀ (b : Bool) (X : Finset (Fin n) × ℕ), X ∈ S.toCellScheme.gradedFaces → X.2 = 1 →
    ∀ (a : Fin S.card ⊕ Fin S.card → ℕ) (F : ℕ → Label.{u}) (c : Label.{u}) (ℓ : ℕ)
      (r : S.toCellScheme.below X → Label.{u}),
      IsSpanRankMember S H T K a → IsPositiveTable H F → IsSelfVisible 1 c → ℓ ≤ H + 1 →
      (∀ i ≤ H, i < ℓ ↔ F i < c) → S.rows.IsLawfulBelow X r →
      (∀ d : S.toCellScheme.below X, min (F (a (sideField b d.1))) c = min (r d) c) →
      ∃ (a' : Fin S.card ⊕ Fin S.card → ℕ) (F' : ℕ → Label.{u}),
        IsSpanRankMember S H T K a' ∧ IsPositiveTable H F' ∧ (∀ x, min (a x) ℓ = min (a' x) ℓ) ∧
        (∀ i < ℓ, F' i = F i) ∧ (∀ i ≤ H, min (F' i) c = min (F i) c) ∧
        (∀ x, min (F' (a' x)) c = min (F (a x)) c) ∧
        ∀ d : S.toCellScheme.below X, F' (a' (sideField b d.1)) = r d

end VaughtConjecture.ProcessRank

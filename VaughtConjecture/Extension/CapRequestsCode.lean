/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequests
import VaughtConjecture.Extension.ProfileTower

/-!
# Cap requests and the code of a profile

Roadmap, Layer 3 (3.1: the catalogue at a grade; 3.3: the private cap, the marker and the
references of (R3) and (R4)).

The construction of `VaughtConjecture.Extension.ProfileTower` sends a profile `P` (a labelling of
the cells of the amalgam of a seed `I`) at the grade `k` to its **code**
`ProfileTower.code (I := I) k P = orbitCode k (hat I k P)`: the splice `hat I k P` keeps `P` at the
cells of grade at most `k` and is `⊥` above, and the orbit code at `k` ranks the values.  Both
steps keep capped correctness (`CapRequests.IsCorrect`) for requests graded by the grades of the
amalgam (`CapRequests.IsGraded`), with no other hypothesis.

* **The splice** (`CapRequests.IsCorrect.hat`): `hat I k P` is the image of `P` under the witness
  of the identity bounded by grade `k`, `d ↦ min (P d) (stepSuppressor k (grade d))`, so
  `CapRequests.IsCorrect.map` applies.
* **The code** (`CapRequests.IsCorrect.code`).  If the grade of the cap is at most `k`, then the
  threshold `N` is at most `k`, and the orbit map at `k` is a witness bounded by grade `k`
  (`Label.isWitness_orbitMap`), so the plain image of the splice is correct
  (`CapRequests.IsCorrect.comp`).  If the grade of the cap is above `k`, the splice is `⊥` at the
  cap, so is its orbit code, and a state with cap `⊥` is correct.
* **The bottom class** (`CapRequests.inBottomClass_code_iff`): the orbit code is `⊥` exactly where
  its argument is, and the splice is `⊥` exactly where `P` is at the cells of grade at most `k`;
  so on a set of cells of grade at most `k` the code is in a bottom class exactly when `P` is.

So the rank normalization of the catalogue does not break correctness: neither the `⊥` clause nor
the reference and marker clauses.  The `⊥` clause is kept because the orbit map reflects `⊥`
and the splice only adds `⊥` above the grade `k`, where it caps the state at `⊥` only if the cap
itself lies above `k`.
-/

universe u

namespace VaughtConjecture.CapRequests

open Label ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {P : Prof I}

/-- The splice of a profile is its image under the identity witness bounded by grade `k`. -/
theorem hat_eq_min (k : ℕ) (P : Prof I) :
    hat I k P = fun d ↦ min (id (P d)) (stepSuppressor k (I.amalgam.toCellScheme.grade d)) := by
  funext d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat, CellScheme.splice_of_le hd, stepSuppressor_of_le hd, min_top_right]
    rfl
  · rw [hat, CellScheme.splice_of_lt (not_le.mp hd), stepSuppressor_of_lt (not_le.mp hd),
      min_bot_right]

/-- **The splice keeps correctness**, for requests graded by the grades of the amalgam. -/
theorem IsCorrect.hat (hs : r.IsCorrect P) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (k : ℕ) : r.IsCorrect (ProfileTower.hat I k P) := by
  rw [hat_eq_min]
  exact hs.map hgr (IsWitness.id_step k)

/-- **The code keeps correctness**: for requests graded by the grades of the amalgam, the code
`orbitCode k (hat I k P)` of a correct profile is correct, at every grade `k`. -/
theorem IsCorrect.code (hs : r.IsCorrect P) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (k : ℕ) : r.IsCorrect (ProfileTower.code (I := I) k P) := by
  by_cases hk : I.amalgam.toCellScheme.grade r.cap ≤ k
  · exact (hs.hat hgr k).comp (isWitness_orbitMap k _) (hgr.le_grade_cap.trans hk)
      hgr.off_le
  · refine isCorrect_of_cap_eq_bot ?_
    change orbitCode k (ProfileTower.hat I k P) r.cap = ⊥
    rw [orbitCode_eq_bot_iff, ProfileTower.hat, CellScheme.splice_of_lt (not_le.mp hk)]

/-- **The code keeps the bottom class** on cells of grade at most `k`: there the code of `P` is in
the class exactly when `P` is. -/
theorem inBottomClass_code_iff {B ZA : Set (Fin I.amalgam.card)} {k : ℕ}
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k) :
    InBottomClass B ZA (ProfileTower.code (I := I) k P) ↔ InBottomClass B ZA P := by
  refine forall₂_congr fun d hd ↦ ?_
  change (orbitCode k (ProfileTower.hat I k P) d = ⊥ ↔ d ∈ ZA) ↔ _
  rw [orbitCode_eq_bot_iff, ProfileTower.hat, CellScheme.splice_of_le (hB d hd)]

/-- **The code keeps admission** on cells of grade at most `k`, for graded requests. -/
theorem Admits.code {B ZA : Set (Fin I.amalgam.card)} (hs : r.Admits B ZA P)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k) :
    r.Admits B ZA (ProfileTower.code (I := I) k P) := fun hcl ↦
  (hs ((inBottomClass_code_iff hB).mp hcl)).code hgr k

end VaughtConjecture.CapRequests

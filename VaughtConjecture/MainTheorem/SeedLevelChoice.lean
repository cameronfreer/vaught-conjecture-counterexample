/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelQuad

/-!
# The re-rendered levels at the seed position, at one choice of height and block bound

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**The choice** (`Seed.seedHeightLevel`, `Seed.seedBlockBound`), functions of the seed and the root
only (not of a state, an ambient labelling or a cap):
* the height `H = #attachment + 1` (the number of cells of the attachment as ladder base data plus
  one; it is the height `Seed.seedHeight` of the earlier choice, `Seed.seedHeightLevel_eq`);
* the block bound `B = max (2 * #attachment) (Seed.seedGridBound)`: at least twice the number of
  cells of the attachment, as the levels ask, and at least the grid bound of the earlier choice, so
  that the compressed labels of the attachment and the code set of its states lie below the grid
  point `ω * B + 2` (`Seed.le_gridPoint_seedBlockBound_of_mem_seedValues`).
Every side condition of the levels holds at every seed and root (`Seed.seedHeightLevel_pos`,
`Seed.card_attachmentBase_le_seedHeightLevel`, `Seed.two_mul_card_le_seedBlockBound`).  The
alternative `Seed.seedBlockBound' = max (2 * #attachment + 1) (Seed.seedGridBound)` exceeds twice
the number of cells strictly (`Seed.two_mul_card_lt_seedBlockBound'`), with the same other side
conditions; it is a function of the seed and the root as well.

**The context lift at the seed position** (`StageType.lvLevel_cappedLift_atSeed`): with exactly
the binders of `StageType.HasLadderGrowthCarriersStableAtSeed` (a legal context on `m + 1` points
at a limit stage with a closed first coatom, a root of positive arity inside it, a one-point coface
`d` of the root face, and requests calibrated on the class with the labels pair correct and the
relative lift on the class), the seed of `StageType.exists_growthSeed_of_isSuccLimit` carries
levels at the choice that lift capped from the context coatom into `(univ, j + 1)` for every
`j + 1 ≤ m + 1`.  Every premise of the chain lemma `Seed.lvLevel_cappedLift'` is one of the binders
or comes from the seed: the legal donor and its root face are the two parts of `d ∈ p.cofaces`, the
face of the amalgam along the root followed by the new point is given by the seed.  No relation
between the threshold and the arity beyond `n + 1 ≤` threshold is used: the equality
`n + 1 = threshold` is allowed.  The lift at the grade `j + 1` passes to every higher level
(`Seed.lvLevel_cappedLift_iff_of_le`), so one level carries the lifts at all the grades below it
(`StageType.lvLevel_cappedLift_atSeed_of_le`), and so does the level with its copies at the mixed
faces (`Seed.lvRep_cappedLift_seedChoice`, through `Seed.ALvl.Good.cappedLift_rep`).

**The onto root.**  At the seed position the root `g : Fin n ↪ Fin m` may be onto; then the
threshold is `n + 1 = m + 1` (`StageType.GrowthRequests.ClassCalibrated.threshold_eq_of_surjective`)
and the second coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`, a statement about
finite sets of points only).  At the grade one the first level lifts capped from the second coatom
(`Seed.lvLevel1_cappedLift_coatom_one_of_surjective`), and so do the higher levels with their
copies (`Seed.lvRep_cappedLift_coatom_one_of_surjective`; the copies have mixed scope, never inside
the donor face, `Seed.ALvl.Good.cappedLift_rep_donor`).  Above the grade one no lift from the
second coatom of the levels is compiled.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-! ### The choice of the height and the block bound -/

/-- **The height of the levels at a seed**: the number of cells of the attachment as ladder base
data plus one. -/
noncomputable def seedHeightLevel : ℕ := (I.attachmentBase g).S.card + 1

/-- **The block bound of the levels at a seed**: the larger of twice the number of cells of the
attachment and the grid bound `Seed.seedGridBound`. -/
noncomputable def seedBlockBound : ℕ := max (2 * (I.attachment g).card) (I.seedGridBound g)

theorem seedHeightLevel_pos : 0 < I.seedHeightLevel g := Nat.succ_pos _

theorem card_attachmentBase_le_seedHeightLevel :
    (I.attachmentBase g).S.card ≤ I.seedHeightLevel g :=
  Nat.le_succ _

/-- The height of the levels is the height `Seed.seedHeight` of the earlier choice. -/
theorem seedHeightLevel_eq : I.seedHeightLevel g = I.seedHeight g := rfl

theorem two_mul_card_le_seedBlockBound : 2 * (I.attachment g).card ≤ I.seedBlockBound g :=
  le_max_left _ _

theorem seedGridBound_le_seedBlockBound : I.seedGridBound g ≤ I.seedBlockBound g :=
  le_max_right _ _

/-- **The values of the earlier choice lie below the grid point at the block bound**: `⊥`, the
compressed labels of the attachment and the code set of its states. -/
theorem le_gridPoint_seedBlockBound_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x ≤ gridPoint 2 (I.seedBlockBound g) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact bot_le
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_le_gridPoint
      ((le_max_left _ _).trans (seedGridBound_le_seedBlockBound I g)) c
  · exact le_gridPoint_of_mem_codeSet
      ((le_max_right _ _).trans (seedGridBound_le_seedBlockBound I g)) hx

/-! ### The alternative block bound with the strict bound -/

/-- **The alternative block bound of the levels at a seed**: the larger of twice the number of
cells of the attachment plus one and the grid bound `Seed.seedGridBound`; it exceeds twice the
number of cells strictly. -/
noncomputable def seedBlockBound' : ℕ :=
  max (2 * (I.attachment g).card + 1) (I.seedGridBound g)

theorem two_mul_card_lt_seedBlockBound' : 2 * (I.attachment g).card < I.seedBlockBound' g :=
  Nat.lt_of_succ_le (le_max_left _ _)

theorem two_mul_card_le_seedBlockBound' : 2 * (I.attachment g).card ≤ I.seedBlockBound' g :=
  (two_mul_card_lt_seedBlockBound' I g).le

theorem seedGridBound_le_seedBlockBound' : I.seedGridBound g ≤ I.seedBlockBound' g :=
  le_max_right _ _

/-- The values of the earlier choice lie below the grid point at the alternative block bound. -/
theorem le_gridPoint_seedBlockBound'_of_mem_seedValues {x : Label.{u}}
    (hx : x ∈ I.seedValues g) : x ≤ gridPoint 2 (I.seedBlockBound' g) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact bot_le
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_le_gridPoint
      ((le_max_left _ _).trans (seedGridBound_le_seedBlockBound' I g)) c
  · exact le_gridPoint_of_mem_codeSet
      ((le_max_right _ _).trans (seedGridBound_le_seedBlockBound' I g)) hx

/-! ### The context lift at every seed, at the choice -/

variable {I g}

/-- **The context lift of the levels at the choice**, at every seed with a donor face `d` that is
a one-point coface of the root face, for requests calibrated on the class with the labels pair
correct and the relative lift on the class, over a root of positive arity. -/
theorem lvLevel_cappedLift_seedChoice {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∀ j, j + 1 ≤ m + 1 →
      (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA Q j).S.rows.CappedLift
        (X := (univ.erase (Fin.last (m + 1)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift' (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hte
    hd.2 hd.1 hn hdA hQ hpair hrel (two_mul_card_le_seedBlockBound I g)

/-! ### Lifts below a level pass to the higher levels -/

/-- **A lift into a pair of grade at most `i + 1` is the same in every level from the grade
`i + 1` on**: the next levels add cells at the grade above only. -/
theorem lvLevel_cappedLift_iff_of_le {H B : ℕ} {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} {i : ℕ} {X : Finset (Fin (m + 2)) × ℕ} {k : ℕ}
    (hki : k ≤ i + 1) (h : X ≤ ((univ : Finset (Fin (m + 2))), k)) :
    ∀ J, i ≤ J → ((I.lvLevel g H B hd Q J).S.rows.CappedLift h ↔
      (I.lvLevel g H B hd Q i).S.rows.CappedLift h)
  | J, hJ => by
    induction J, hJ using Nat.le_induction with
    | base => exact Iff.rfl
    | succ J hiJ ih =>
      exact (ALvl.cappedLift_nS_iff (B := B) (I.lvLevel g H B hd Q J)
        (I.lvCat g B hd Q (J + 2)) h fun h' ↦ absurd h'.2 (by simp only; omega)).trans ih

/-! ### The onto root at the grade one -/

/-- **The first level lifts from the second coatom at the grade one for an onto root**: the
second coatom is then the donor face (`Seed.donorFace_eq_coatom_of_surjective`), and the ladder
base lifts from the donor face into `(univ, 1)` (`Scheme.cappedLift_ladderBase_rankMember` with
`Seed.cappedLift_attachment_univ_one`). -/
theorem lvLevel1_cappedLift_coatom_one_of_surjective {H : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hg : Function.Surjective g)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.lvLevel1 g H).S.rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last m)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hD
  have hD1 : 1 ≤ #D := by rw [hD, card_map, card_univ, Fintype.card_fin]; omega
  have hXU : ((D, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨subset_univ _, le_rfl⟩
  have hX : ¬ (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤ (D, 1) :=
    fun h ↦ map_extendByLast_ne_univ g (univ_subset_iff.mp h.1)
  have hl : (I.lvLevel1 g H).S.rows.CappedLift hXU :=
    Scheme.cappedLift_ladderBase_rankMember (hS := (I.attachmentBase g).noFull)
      (I.attachmentBase g).wf hH hcard hXU hX
      (cappedLift_attachment_univ_one hdF hrF hr1 hdF hD1 (.inr subset_rfl))
  have key : ∀ (W : Finset (Fin (m + 2)))
      (h : ((W, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1)),
      W = D → (I.lvLevel1 g H).S.rows.CappedLift h := by
    rintro W h rfl
    exact hl
  exact key _ _ (donorFace_eq_coatom_of_surjective g hg).symm

/-! ### The replicated levels -/

/-- **The replicated level lifts from a pair inside the donor face** into a pair of full scope
wherever the level does: the copies have mixed scope, never inside the donor face. -/
theorem ALvl.Good.cappedLift_rep_donor {H B j : ℕ}
    {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} {N : I.ALvl g H j}
    (hN : N.Good B A) {X Y : Finset (Fin (m + 2)) × ℕ} (h : X ≤ Y) (hY : Y.1 = univ)
    (hX : X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hT : N.S.rows.CappedLift h) : hN.rep.rows.CappedLift h :=
  Scheme.cappedLift_mirror_of (fun _ hU ↦ ne_univ_of_mem_mixedFaces hU) h hY
    (fun _ hU hsub ↦ ((I.mem_mixedFaces g).mp hU).2.2.2 (hsub.trans hX)) hT

/-- **The replicated level at the grade `J + 1 ≤ m + 2` lifts from the context coatom at every
grade `j + 1 ≤ min (J + 1) (m + 1)`**, at the choice, at every seed with the data of the seed
position. -/
theorem lvRep_cappedLift_seedChoice {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) (J : ℕ)
    (hJ : J + 1 ≤ m + 2) (j : ℕ) (hjJ : j ≤ J) (hjm : j + 1 ≤ m + 1) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound I g) (hd := hdA) J hJ).rep.rows.CappedLift
        (X := (univ.erase (Fin.last (m + 1)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  ALvl.Good.cappedLift_rep _ _ rfl subset_rfl
    ((lvLevel_cappedLift_iff_of_le le_rfl _ J hjJ).mpr
      (lvLevel_cappedLift_seedChoice hte hd hn hdA hpair hQ hrel j hjm))

/-- **The replicated level lifts from the second coatom at the grade one for an onto root**, at
every grade `J + 1 ≤ m + 2` (`Seed.lvLevel1_cappedLift_coatom_one_of_surjective`, carried to the
level at `J + 1` by `Seed.lvLevel_cappedLift_iff_of_le` and to its copies by
`Seed.ALvl.Good.cappedLift_rep_donor`). -/
theorem lvRep_cappedLift_coatom_one_of_surjective {p : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) (J : ℕ) (hJ : J + 1 ≤ m + 2) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound I g) (hd := hdA) J hJ).rep.rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), 1))
        (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  ALvl.Good.cappedLift_rep_donor _ _ rfl
    (donorFace_eq_coatom_of_surjective g hg).symm.subset
    ((lvLevel_cappedLift_iff_of_le (i := 0) le_rfl _ J (Nat.zero_le J)).mpr
      (lvLevel1_cappedLift_coatom_one_of_surjective (seedHeightLevel_pos I g)
        (card_attachmentBase_le_seedHeightLevel I g) hg (donor_mem_faces hdA)
        (root_mem_faces hte) (by rw [card_root]; exact hn)))

end Seed

namespace StageType

namespace GrowthRequests

/-- **At an onto root the threshold is the arity of the donor**: requests calibrated on the class
have `n + 1 ≤` threshold, the threshold is the grade of a cell of the context on `m + 1` points,
and an onto root `Fin n ↪ Fin m` has `m ≤ n`; so `n = m` and the threshold is `n + 1`. -/
theorem ClassCalibrated.threshold_eq_of_surjective {α : Ordinal.{u}} {n m : ℕ}
    {t' : StageType.{u} α (m + 1)} {g : Fin n ↪ Fin m} {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) : n = m ∧ Q.threshold = n + 1 := by
  have hnm : m ≤ n := by simpa using Fintype.card_le_of_surjective g hg
  have hmn : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  have h1 := hQ.arity
  have h2 := t'.grade_le Q.cap
  unfold threshold at h1 ⊢
  omega

end GrowthRequests

/-! ### The context lift at the seed position -/

/-- **The context lift of the levels at the seed position**, with exactly the binders of
`StageType.HasLadderGrowthCarriersStableAtSeed`: the seed of
`StageType.exists_growthSeed_of_isSuccLimit` has the context as its first coatom type and `d` as
the face of its amalgam along the root followed by the new point, and its levels at the choice
`Seed.seedHeightLevel`, `Seed.seedBlockBound` lift capped from the context coatom into
`(univ, j + 1)` for every `j + 1 ≤ m + 1` (`Seed.lvLevel_cappedLift'`). -/
theorem lvLevel_cappedLift_atSeed {α : Ordinal.{u}} {n m : ℕ} (t' : StageType.{u} α (m + 1))
    (g : Fin n ↪ Fin m) (p' : StageType.{u} α m) (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal)
    (hp' : restrictFace Fin.castSuccEmb t' = some p') (p : StageType.{u} α n)
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∃ (I : Seed.{u} α m) (hI : I.left = t')
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d),
      ∀ j, j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA (hI ▸ Q) j).S.rows.CappedLift
          (X := (univ.erase (Fin.last (m + 1)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  exact ⟨I, rfl, hdA, Seed.lvLevel_cappedLift_seedChoice hte hd hn hdA hpair hQ hrel⟩

/-- **The context lift at the seed position in one level**: as
`StageType.lvLevel_cappedLift_atSeed`, with the lifts at all the grades
`j + 1 ≤ min (J + 1) (m + 1)` read in the one level at the grade `J + 1`
(`Seed.lvLevel_cappedLift_iff_of_le`). -/
theorem lvLevel_cappedLift_atSeed_of_le {α : Ordinal.{u}} {n m : ℕ}
    (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m) (p' : StageType.{u} α m)
    (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal)
    (hp' : restrictFace Fin.castSuccEmb t' = some p') (p : StageType.{u} α n)
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∃ (I : Seed.{u} α m) (hI : I.left = t')
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d),
      ∀ J j, j ≤ J → j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA (hI ▸ Q) J).S.rows.CappedLift
          (X := (univ.erase (Fin.last (m + 1)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨I, hI, hdA, h⟩ :=
    lvLevel_cappedLift_atSeed t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  exact ⟨I, hI, hdA, fun J j hjJ hjm ↦
    (Seed.lvLevel_cappedLift_iff_of_le le_rfl _ J hjJ).mpr (h j hjm)⟩

end StageType

end VaughtConjecture

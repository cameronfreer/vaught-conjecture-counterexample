/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CappedDonorReading
import VaughtConjecture.Extension.Gate

/-!
# Gates with the capped reading

Roadmap, Layer 3, 3.2 (the ordinary construction (R1)) and 3.3 (the recovery statements, item 1:
agreement below a cutoff); the vocabulary of `VaughtConjecture.Extension.Gate` (private cells,
donor cells, display, readers) and the reference data of
`VaughtConjecture.Extension.CappedDonorReading` (cap, blocks, reference cells, the cut, the capped
reading).

A gate in the sense of `CellScheme.Rows.IsGate` reads every donor cell exactly: a donor label
`vr_N(w z, i)` through its anchor `z` is read as `vr_N` of the reading of `z`, and a donor label
at least the private cap through a private cell at least the cap.  The capped reading of
`CappedDonorReading.PrivateReference.reading` caps every reading by the cut.  This file states
the gate condition for the capped reading and proves recovery below the cut.

**The row of a cell, as a labelling** (`CellScheme.Rows.rowAt R K`): the row of `K` at the cells
below `K`, and `⊥` elsewhere.

**Capped gates** (`CellScheme.Rows.IsCappedGate R K P S Q w`), for reference data `P` whose cap and
reference cells are private cells (the set `S`) below `K`, with full grade the grade of `K`: every
donor cell (the set `Q`) lies below `K`, and the row of `K` at a donor cell `e` outside `S`, capped
by the **cut read by `K`**, `P.cut (R.rowAt K)`, is the capped reading, through the row of `K`
itself, of the display label `w e`:
`min (R.row K e) (P.cut (R.rowAt K)) = P.reading (R.rowAt K) (w e)`.  So the row is `⊥` at a donor
label `⊥`; at `ω * b + i` (a requested block `b`, `i ≤ N`) it is the replacement `vr_N(i, ·)` of the
row of `K` at the reference cell of `b` when that lies below the cut read by `K`, and at least that
cut otherwise; and at `⊤` it is at least that cut.  The display labels of the donor cells outside
`S` read in the blocks, and the display reads itself as the donor capped by its cut:
`P.reading w (w e) = min (w e) (P.cut w)` (with the margin this is
`CappedDonorReading.PrivateReference.HasMargin.reading_eq_min`).

**Recovery below the cut** (`CellScheme.Rows.IsLawful.recover_of_readsOnly_capped`).  Let `q` be
lawful, literally the display on the private cells, not `⊥` at a cell `G` whose row reads only a
set of capped gates and reads one of them at least as `G` itself.  Availability for the private cap
gives a member `K` with `w C ≤ q K`; one witness at `K` commutes with the capped reading below
`q K` (`CellScheme.Rows.IsLawful.min_reading_rowAt`), and the cut of the display is at most
`w C ≤ q K`.  So `q` agrees with the display on every donor cell below the cut:
`min (q e) (P.cut w) = min (w e) (P.cut w)`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside `VaughtConjecture.Extension.Gate`.

## References

Witnesses are [Kni26, Definition 2.3.9], visibility replacement [Kni26, Definition 2.2.3], and
lawful sections, with locality and availability, [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Finset Label CappedDonorReading

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {G K : ι}
  {P : PrivateReference.{u} ι} {S Q : Set ι} {w q : ι → Label.{u}}

/-- **The row of `K` as a labelling of all cells**: the row of `K` below `K`, `⊥` elsewhere. -/
noncomputable def rowAt (R : D.Rows.{u}) (K : ι) (x : ι) : Label.{u} := by
  classical
  exact if h : x ∈ D.below (D.gradedIndex K) then R.row K ⟨x, h⟩ else ⊥

/-- The row of `K` as a labelling, at a cell below `K`, is the row of `K` there. -/
theorem rowAt_of_mem (R : D.Rows.{u}) {x : ι} (h : x ∈ D.below (D.gradedIndex K)) :
    R.rowAt K x = R.row K ⟨x, h⟩ := by
  classical
  simp [rowAt, h]

/-- **A capped gate**: the cap and the reference cells of `P` are private cells below `K`, the
cap has the grade of `K` and scope inside that of `K`, the full grade of `P` is the grade of `K`,
every donor cell lies below `K`, and the row of `K` reads every donor cell outside the private
cells by the capped reading of the display label through the row of `K`.  The display labels of
those donor cells read in the blocks of `P`, and the capped reading through the display is the
display label capped by the cut. -/
structure IsCappedGate (R : D.Rows.{u}) (K : ι) (P : PrivateReference.{u} ι) (S Q : Set ι)
    (w : ι → Label.{u}) : Prop where
  /-- The cap is a private cell. -/
  cap_mem : P.cap ∈ S
  /-- The reference cells of the requested blocks are private cells. -/
  ref_mem : ∀ b ∈ P.blocks, P.ref b ∈ S
  /-- Every private cell lies below `K`. -/
  private_le : ∀ x ∈ S, D.gradedIndex x ≤ D.gradedIndex K
  /-- The scope of the cap lies in that of `K`. -/
  scope_cap_subset : D.scope P.cap ⊆ D.scope K
  /-- The cap has the grade of `K`. -/
  grade_cap : D.grade P.cap = D.grade K
  /-- The full grade of `P` is the grade of `K`. -/
  fullGrade_eq : P.fullGrade = D.grade K
  /-- The cap is not `⊥` in the display. -/
  cap_ne_bot : w P.cap ≠ ⊥
  /-- Every donor cell lies below `K`. -/
  donor_le : ∀ e ∈ Q, D.gradedIndex e ≤ D.gradedIndex K
  /-- The display labels of the donor cells outside the private cells read in the blocks. -/
  readsInBlocks : ∀ e ∈ Q, e ∉ S → ∀ o : Ordinal.{u}, w e = o →
    o / Ordinal.omega0 ∈ P.blocks ∧ o % Ordinal.omega0 ≤ P.fullGrade
  /-- The capped reading through the display is the display label capped by the cut. -/
  reading_eq : ∀ e ∈ Q, e ∉ S → P.reading w (w e) = min (w e) (P.cut w)
  /-- The row of `K` reads every donor cell outside the private cells by the capped reading, up to
  the cut read by `K`. -/
  reads : ∀ e (he : e ∈ Q), e ∉ S →
    min (R.row K ⟨e, donor_le e he⟩) (P.cut (R.rowAt K)) = P.reading (R.rowAt K) (w e)

/-! ### One witness commutes with the capped reading -/

section Witness

/-- Capping distributes over a minimum. -/
private theorem min_min_cap (a b c : Label.{u}) : min (min a b) c = min (min a c) (min b c) :=
  inf_inf_distrib_right a b c

variable {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} {h : Label.{u}} {r : ι → Label.{u}}

/-- **The cut, through one witness**: if `σ` sends `r` to `q` capped at `h` at the cap and at
the reference cells of the requested blocks, it sends the cut of `r` to the cut of `q`, capped at
`h`, when `h` is self-visible at the full grade and at most `g` there. -/
theorem _root_.VaughtConjecture.CappedDonorReading.PrivateReference.min_cut_eq
    (hσ : IsWitness g σ) (hh : IsSelfVisible P.fullGrade h) (hhg : h ≤ g P.fullGrade)
    (hC : min (σ (r P.cap)) h = min (q P.cap) h)
    (href : ∀ b ∈ P.blocks, min (σ (r (P.ref b))) h = min (q (P.ref b)) h) :
    min (σ (P.cut r)) h = min (P.cut q) h := by
  have hsup : σ (P.blocks.sup fun b ↦ visibilityReplace P.fullGrade P.fullGrade (r (P.ref b))) =
      P.blocks.sup fun b ↦ σ (visibilityReplace P.fullGrade P.fullGrade (r (P.ref b))) :=
    Finset.apply_sup_eq_sup_comp_of_linearOrder σ hσ.monotone hσ.map_bot
  have hpt : ∀ b ∈ P.blocks,
      min (σ (visibilityReplace P.fullGrade P.fullGrade (r (P.ref b)))) h =
        min (visibilityReplace P.fullGrade P.fullGrade (q (P.ref b))) h := fun b hb ↦
    hσ.min_apply_visibilityReplace hh hhg (href b hb) le_rfl
  have hsupcap : ∀ f : Ordinal.{u} → Label.{u},
      min (P.blocks.sup f) h = P.blocks.sup fun b ↦ min (f b) h := fun f ↦
    Finset.sup_inf_distrib_right P.blocks f h
  rw [PrivateReference.cut, PrivateReference.cut, hσ.monotone.map_min, hsup,
    min_min_cap, min_min_cap _ _ h, hC, hsupcap, hsupcap,
    Finset.sup_congr rfl hpt]

/-- **The capped reading, through one witness**: if `σ` sends `r` to `q` capped at `h` at the cap
and at the reference cells of the requested blocks, it sends the capped reading through `r` of
any label reading in the blocks to the capped reading through `q`, capped at `h`. -/
theorem _root_.VaughtConjecture.CappedDonorReading.PrivateReference.min_reading_eq
    (hσ : IsWitness g σ) (hh : IsSelfVisible P.fullGrade h) (hhg : h ≤ g P.fullGrade)
    (hC : min (σ (r P.cap)) h = min (q P.cap) h)
    (href : ∀ b ∈ P.blocks, min (σ (r (P.ref b))) h = min (q (P.ref b)) h) {y : Label.{u}}
    (hy : ∀ o : Ordinal.{u}, y = o →
      o / Ordinal.omega0 ∈ P.blocks ∧ o % Ordinal.omega0 ≤ P.fullGrade) :
    min (σ (P.reading r y)) h = min (P.reading q y) h := by
  have hcut := P.min_cut_eq hσ hh hhg hC href
  induction y using recBotCoeTop with
  | bot => simp [hσ.map_bot]
  | top => simpa using hcut
  | coe o =>
    obtain ⟨b, hb, n, hn, rfl⟩ := P.exists_eq_of_readsInBlocks (hy o rfl)
    rw [PrivateReference.reading_omega0_mul_add, PrivateReference.reading_omega0_mul_add,
      hσ.monotone.map_min, min_min_cap, min_min_cap _ _ h,
      hσ.min_apply_visibilityReplace hh hhg (href b hb) hn, hcut]

end Witness

/-- The cut depends on the labelling only at the cap and at the reference cells of the requested
blocks. -/
theorem _root_.VaughtConjecture.CappedDonorReading.PrivateReference.cut_congr
    {r : ι → Label.{u}} (hC : q P.cap = r P.cap)
    (href : ∀ b ∈ P.blocks, q (P.ref b) = r (P.ref b)) : P.cut q = P.cut r := by
  rw [PrivateReference.cut, PrivateReference.cut, hC,
    Finset.sup_congr rfl fun b hb ↦ by rw [href b hb]]

/-- The capped reading depends on the labelling only at the cap and at the reference cells of the
requested blocks, for labels reading in the blocks. -/
theorem _root_.VaughtConjecture.CappedDonorReading.PrivateReference.reading_congr
    {r : ι → Label.{u}} (hC : q P.cap = r P.cap) (href : ∀ b ∈ P.blocks, q (P.ref b) = r (P.ref b))
    {y : Label.{u}} (hy : ∀ o : Ordinal.{u}, y = o →
      o / Ordinal.omega0 ∈ P.blocks ∧ o % Ordinal.omega0 ≤ P.fullGrade) :
    P.reading q y = P.reading r y := by
  have hcut : P.cut q = P.cut r := P.cut_congr hC href
  induction y using recBotCoeTop with
  | bot => rfl
  | top => exact hcut
  | coe o =>
    obtain ⟨b, hb, n, -, rfl⟩ := P.exists_eq_of_readsInBlocks (hy o rfl)
    rw [PrivateReference.reading_omega0_mul_add, PrivateReference.reading_omega0_mul_add, hcut,
      href b hb]

namespace IsLawful

/-- **Recovery below the cut through capped gates.**  Let the row of `G` read only `T` at its
graded index, and read some `K ∈ T` of that graded index at least as `G` itself, and let every
member of `T` be a capped gate for the reference data `P`, the private cells `S`, the donor cells
`Q` and the display `w`.  A lawful labelling `q`, literally `w` on `S` and not `⊥` at `G`, agrees
with `w` on every donor cell below the cut of the display. -/
theorem recover_of_readsOnly_capped {T : Set ι} (hq : R.IsLawful q) (honly : R.ReadsOnly G T)
    (hT : ∀ u ∈ T, R.IsCappedGate u P S Q w) (hK : K ∈ T)
    (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩)
    (hlit : ∀ x ∈ S, q x = w x) (hG : q G ≠ ⊥) :
    ∀ e ∈ Q, min (q e) (P.cut w) = min (w e) (P.cut w) := by
  have hgK := hT K hK
  have hCG : D.scope P.cap ⊆ D.scope G :=
    hgK.scope_cap_subset.trans (congrArg Prod.fst hKG).le
  have hgr : D.grade P.cap = D.grade G := hgK.grade_cap.trans (congrArg Prod.snd hKG)
  obtain ⟨u, hu, -, hle⟩ := hq.exists_mem_le_of_readsOnly honly hK hKG hrow hG hCG hgr
  have hgu := hT u hu
  rw [hlit _ hgu.cap_mem] at hle
  have hcut : P.cut w ≤ q u := (min_le_left _ _).trans hle
  obtain ⟨g, σ, hσ, hgN, heq⟩ := hq.exists_gateWitness u
  have hh : IsSelfVisible P.fullGrade (q u) := hgu.fullGrade_eq ▸ hq.orderly u
  have hhg : q u ≤ g P.fullGrade := hgu.fullGrade_eq ▸ hgN
  have hS : ∀ x ∈ S, min (σ (R.rowAt u x)) (q u) = min (q x) (q u) := fun x hx ↦ by
    rw [rowAt_of_mem R (hgu.private_le x hx)]
    exact (heq ⟨x, hgu.private_le x hx⟩).symm
  intro e he
  by_cases heS : e ∈ S
  · rw [hlit e heS]
  have hy := hgu.readsInBlocks e he heS
  have hC' := hS _ hgu.cap_mem
  have href' : ∀ b ∈ P.blocks, min (σ (R.rowAt u (P.ref b))) (q u) = min (q (P.ref b)) (q u) :=
    fun b hb ↦ hS _ (hgu.ref_mem b hb)
  have hcutq : P.cut q = P.cut w :=
    P.cut_congr (hlit _ hgu.cap_mem) (fun b hb ↦ hlit _ (hgu.ref_mem b hb))
  -- The cut read by `u`, decoded, is at least the cut of the display.
  have hσcut : min (σ (P.cut (R.rowAt u))) (P.cut w) = P.cut w := by
    have h := P.min_cut_eq hσ hh hhg hC' href'
    rw [hcutq, min_eq_left hcut] at h
    rcases lt_or_eq_of_le hcut with hlt | heq'
    · rw [left_eq_of_min_eq_of_lt h hlt, min_self]
    · rw [heq'] at h ⊢
      exact min_eq_right (min_eq_right_iff.mp h)
  have hread : min (σ (P.reading (R.rowAt u) (w e))) (q u) = min (P.reading w (w e)) (q u) := by
    rw [P.min_reading_eq hσ hh hhg hC' href' hy,
      P.reading_congr (hlit _ hgu.cap_mem) (fun b hb ↦ hlit _ (hgu.ref_mem b hb)) hy]
  calc min (q e) (P.cut w) = min (min (q e) (q u)) (P.cut w) := by
        rw [min_assoc, min_eq_right hcut]
    _ = min (min (σ (R.row u ⟨e, hgu.donor_le e he⟩)) (q u)) (P.cut w) := by
        rw [heq ⟨e, hgu.donor_le e he⟩]
    _ = min (min (σ (R.row u ⟨e, hgu.donor_le e he⟩)) (σ (P.cut (R.rowAt u)))) (P.cut w) := by
        rw [min_assoc, min_eq_right hcut, min_assoc, hσcut]
    _ = min (min (σ (P.reading (R.rowAt u) (w e))) (q u)) (P.cut w) := by
        rw [← hσ.monotone.map_min, hgu.reads e he heS, min_assoc, min_eq_right hcut]
    _ = min (w e) (P.cut w) := by
        rw [hread, min_assoc, min_eq_right hcut, hgu.reading_eq e he heS, min_assoc, min_self]

end IsLawful

end VaughtConjecture.CellScheme.Rows

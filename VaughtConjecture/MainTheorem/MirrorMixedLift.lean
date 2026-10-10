/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.MirrorMixedDecode

/-!
# The lift from a mixed face of a mirrored scheme into a larger face

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces, for any scheme over the attachment
mirrored at the mixed faces of the seed).

**The lift** (`Seed.cappedLift_mirror_mixed_face`).  Let `T` be a consistent scheme over the
attachment (its cells of proper scope are the cells of the attachment `att e`), with ladder points
`lad p` and cells of full scope at the grades `2, …, j` reading the ladder through one member
(`hread`), agreeing at shadows (`hagree`) and with twins (`htwin`) as in
`VaughtConjecture.MainTheorem.MirrorMixedDecode`.  For a mixed face `U ⊆ W` and `1 ≤ j ≤ |U|`, given
a choice `τ` of a cell at `W` with original `v` for every cell `v` of full scope of `T` of grade at
most `j` (the cell itself when `W` is the ground set, its copy at `W` when `W` is mixed), the
mirrored scheme lifts capped from `(U, j)` to `(W, j)`.  The construction is that of
`Seed.cappedLift_mixed_face`: at every grade a dominating cell of full scope (largest copy at `U`;
at the grade one the top rung of the member of the shape of the copied ladder), a capped decoder at
its copy, and the lift reading every cell through the cell at `W` of the dominating cell of its
grade.

`Seed.cappedLift_mirror_mixed_univ` (`W` the ground set) and `Seed.cappedLift_mirror_mixed_mixed`
(`W` a mixed face).

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {T : Scheme.{u} (m + 2)}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ I.mixedFaces g, ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin (m + 2))}
  {att : Fin (I.attachment g).card → Fin T.card}
  {lad : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H →
    Fin T.card}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))

variable (hmix) in
open Classical in
/-- The copy at `U` of a cell of full scope of grade at most `|U|`; the cell itself otherwise. -/
noncomputable def mCpy (hU : U ∈ I.mixedFaces g) (v : Fin T.card) :
    Fin (Scheme.mirror hmix).card :=
  if h : T.toCellScheme.scope v = univ ∧ T.toCellScheme.grade v ≤ #U then
    mCopy hmix hU v h.1 h.2 else Fin.castAdd _ v

theorem mCpy_eq (hU : U ∈ I.mixedFaces g) {v : Fin T.card} {k : ℕ}
    (hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    mCpy hmix hU v = mCopyFull hmix hU v hv hk := by
  classical
  unfold mCpy
  rw [dite_eq_left ⟨congrArg Prod.fst hv, (congrArg Prod.snd hv).trans_le hk⟩]
  rfl

theorem mirrorOrig_mCpy (hU : U ∈ I.mixedFaces g) (v : Fin T.card) :
    T.mirrorOrig (I.mixedFaces g) (mCpy hmix hU v) = v := by
  classical
  unfold mCpy
  split_ifs with h
  · exact mirrorOrig_mCopy hU _ _ _
  · exact Scheme.mirrorOrig_castAdd _ _ _

/-- The cells of the mirrored scheme of scope inside the context face or the donor face are cells
of the attachment. -/
theorem exists_att_of_scope
    (hcells : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (z : Fin (Scheme.mirror hmix).card)
    (hz : (Scheme.mirror hmix).toCellScheme.scope z ⊆
        univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      (Scheme.mirror hmix).toCellScheme.scope z ⊆
        univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    ∃ e, z = Fin.castAdd _ (att e) := by
  change Fin (T.card + T.copyCount (I.mixedFaces g)) at z
  induction z using Fin.addCases with
  | right i =>
    exfalso
    have hU := (I.mem_mixedFaces g).mp
      (show (Scheme.mirror hmix).toCellScheme.scope (Fin.natAdd _ i) ∈ I.mixedFaces g by
        rw [Scheme.scope_mirror_natAdd]; exact ((T.copyEquiv _).symm i).2.1)
    exact hz.elim hU.2.2.1 hU.2.2.2
  | left x =>
    have hsc : (Scheme.mirror hmix).toCellScheme.scope (Fin.castAdd _ x) = T.toCellScheme.scope x :=
      congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd (hmix := hmix) x)
    have hne : T.toCellScheme.scope x ≠ univ := fun he ↦ by
      rw [hsc, he] at hz
      rcases hz with h | h
      · exact map_castSuccEmb_ne_univ (univ_subset_iff.mp h)
      · exact map_extendByLast_ne_univ g (univ_subset_iff.mp h)
    obtain ⟨e, rfl⟩ := hcells x hne
    exact ⟨e, rfl⟩

/-- The cells of the mirrored scheme: of full scope at their grade, or cells of the attachment. -/
theorem mirror_cell_cases_att
    (hcells : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (z : Fin (Scheme.mirror hmix).card) :
    (∃ v, T.mirrorOrig (I.mixedFaces g) z = v ∧
        T.toCellScheme.gradedIndex v =
          ((univ : Finset (Fin (m + 2))), (Scheme.mirror hmix).toCellScheme.grade z)) ∨
      ∃ e, z = Fin.castAdd _ (att e) := by
  rcases mirror_cell_cases (hmix := hmix) z with h | ⟨x, rfl, hx⟩
  · exact .inl h
  · obtain ⟨e, rfl⟩ := hcells x hx
    exact .inr ⟨e, rfl⟩


set_option quotPrecheck false in
/-- The mirrored scheme. -/
local notation "𝔼" => Scheme.mirror hmix

/-- **The lift from a mixed face into a larger face** of a mirrored scheme over the attachment (see
the module docstring). -/
theorem cappedLift_mirror_mixed_face (hH : 0 < H)
    (hcons : T.rows.IsConsistent) (hpos : ∀ d, 1 ≤ T.toCellScheme.grade d)
    (hatt : ∀ e, T.toCellScheme.gradedIndex (att e) = (I.attachment g).toCellScheme.gradedIndex e)
    (hcells : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p) (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 2))), 1) →
      ∃ p, x = lad p)
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    (hagree : ∀ f u K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      T.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k → ∃ v,
        T.rowAt u (lad v) = T.rowAt u (att e) ∧
        min (T.rowAt f (lad v)) (T.rowAt f u) = min (T.rowAt f (att e)) (T.rowAt f u))
    (htwin : ∀ f K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      2 ≤ k → k ≤ K → ∀ e, (I.attachment g).toCellScheme.grade e = k →
      ∃ et, T.toCellScheme.gradedIndex et = ((univ : Finset (Fin (m + 2))), k) ∧
        T.rowAt f (att e) ≤ T.rowAt f et)
    (hU : U ∈ I.mixedFaces g) {W : Finset (Fin (m + 2))} (hUW : U ⊆ W)
    (τ : Fin T.card → Fin (𝔼).card) (hτo : ∀ v, T.mirrorOrig (I.mixedFaces g) (τ v) = v) {j : ℕ}
    (hτg : ∀ v k, T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k) → k ≤ j →
      (𝔼).toCellScheme.gradedIndex (τ v) = (W, k))
    (hexist : ∀ k, 2 ≤ k → k ≤ j → ∃ f, T.toCellScheme.gradedIndex f =
      ((univ : Finset (Fin (m + 2))), k))
    (hj1 : 1 ≤ j) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ := by
  classical
  have hXY : ((U, j) : Finset (Fin (m + 2)) × ℕ) ≤ (W, j) := ⟨hUW, le_rfl⟩
  have hU1 : 1 ≤ #U := hj1.trans hjU
  have hgiA (e : Fin (I.attachment g).card) : (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (att e)) =
      (I.attachment g).toCellScheme.gradedIndex e :=
    (Scheme.gradedIndex_mirror_castAdd (hmix := hmix) (att e)).trans (hatt e)
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  -- total labellings
  obtain ⟨P, hPd⟩ : ∃ P : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below (U, j)), P d = p ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ p, fun d hd ↦ CellScheme.Rows.extendBot_of_mem p hd⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below (W, j)), Q d = q ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ q, fun d hd ↦ CellScheme.Rows.extendBot_of_mem q hd⟩
  have hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d := by
    have e : (fun d : (𝔼).toCellScheme.below (U, j) ↦ P d) = p := funext fun d ↦ hPd d d.2
    rw [e]; exact hp
  have hQ : (𝔼).rows.IsLawfulBelow (W, j) fun d ↦ Q d := by
    have e : (fun d : (𝔼).toCellScheme.below (W, j) ↦ Q d) = q := funext fun d ↦ hQd d d.2
    rw [e]; exact hq
  have hpq' (d) (hd : d ∈ (𝔼).toCellScheme.below (U, j)) : min (Q d) c = min (P d) c := by
    rw [hQd d (le_trans hd hXY), hPd d hd]
    exact hpq ⟨d, hd⟩
  -- the member of the copied ladder
  obtain ⟨a, ha⟩ : ∃ a : Scheme.RankMember (I.attachmentBase g).S H, ∀ v,
      P (mCopyLadder hmix hlad hU v) ≤
        P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)) := by
    rcases mCopyLadder_exists_shape hH hlad hrowLL hU hP
        (show ((U, 1) : Finset (Fin (m + 2)) × ℕ) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
      hall | ⟨a, gg, σ, hwit, hch, -⟩
    · obtain ⟨a0⟩ := (inferInstance : Nonempty (Scheme.RankMember (I.attachmentBase g).S H))
      exact ⟨a0, fun v ↦ by rw [hall v]; exact bot_le⟩
    · refine ⟨a, fun v ↦ ?_⟩
      rw [hch v, hch _]
      refine min_le_min_right _ (hwit.monotone (monotone_ladderSource H ?_))
      have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        ((a, Sum.inl ⟨H - 1, by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H)
      change _ ≤ ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
        (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
        (a, Sum.inl ⟨H - 1, by omega⟩)
      rw [h]
      change _ ≤ H - 1 + 1
      have := ladderIndex_le (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (ceil := Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
        a v
      omega
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  -- the dominating cells
  have hexu : ∀ k : ℕ, ∃ u₀ : Fin T.card, 1 ≤ k → k ≤ j →
      T.toCellScheme.gradedIndex u₀ = ((univ : Finset (Fin (m + 2))), k) ∧
      (k = 1 → u₀ = lad top) ∧
      ∀ w, T.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k) →
        P (mCpy hmix hU w) ≤ P (mCpy hmix hU u₀) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ j
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        refine ⟨lad top, fun _ _ ↦ ⟨hlad top, fun _ ↦ rfl, fun w hw ↦ ?_⟩⟩
        obtain ⟨v, rfl⟩ := hone w hw
        rw [mCpy_eq hU (hlad v) hU1, mCpy_eq hU (hlad top) hU1]
        exact ha v
      · obtain ⟨f0, hf0⟩ := hexist k hk2 hk.2
        obtain ⟨u₀, hu₀, hmax⟩ := (univ.filter fun w : Fin T.card ↦
            T.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)).exists_max_image
          (fun w ↦ P (mCpy hmix hU w)) ⟨f0, by simp [hf0]⟩
        rw [mem_filter] at hu₀
        exact ⟨u₀, fun _ _ ↦ ⟨hu₀.2, fun h ↦ absurd h (by omega),
          fun w hw ↦ hmax w (by simp [hw])⟩⟩
    · exact ⟨lad top, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
  choose u hu using hexu
  -- the decoders at their copies
  have hexθ : ∀ k : ℕ, ∃ θ : Label.{u} → Label.{u}, 1 ≤ k → k ≤ j →
      IsWitness (stepSuppressor k) θ ∧ (∀ x, θ x ≤ P (mCpy hmix hU (u k))) ∧
      ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (mCpy hmix hU (u k))),
        θ ((𝔼).rowAt (mCpy hmix hU (u k)) d) = min (P d) (P (mCpy hmix hU (u k))) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ j
    · have hcu := mCpy_eq (hmix := hmix) hU (hu k hk.1 hk.2).1 (hk.2.trans hjU)
      have hmem : mCpy hmix hU (u k) ∈ (𝔼).toCellScheme.below (U, j) := by
        rw [hcu, CellScheme.mem_below, gradedIndex_mCopyFull]; exact ⟨subset_rfl, hk.2⟩
      have hgr : (𝔼).toCellScheme.grade (mCpy hmix hU (u k)) = k := by
        rw [hcu]; exact congrArg Prod.snd (gradedIndex_mCopyFull hU _ _ _)
      obtain ⟨θ, hθw, hθle, hθr⟩ := Scheme.exists_cappedDecoder_below hP hmem hgr
      exact ⟨θ, fun _ _ ↦ ⟨hθw, hθle, hθr⟩⟩
    · exact ⟨id, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
  choose θ hθ using hexθ
  -- the lift
  set r : Fin (𝔼).card → Label.{u} := fun d ↦ θ ((𝔼).toCellScheme.grade d)
    ((𝔼).rowAt (τ (u ((𝔼).toCellScheme.grade d))) d) with hr
  have hrdef (d) : r d = θ ((𝔼).toCellScheme.grade d)
      ((𝔼).rowAt (τ (u ((𝔼).toCellScheme.grade d))) d) := rfl
  have hgY (d) (hd : d ∈ (𝔼).toCellScheme.below (W, j)) :
      1 ≤ (𝔼).toCellScheme.grade d ∧ (𝔼).toCellScheme.grade d ≤ j :=
    ⟨hpos (T.mirrorOrig (I.mixedFaces g) d), hd.2⟩
  have hgiu (k) (h1 : 1 ≤ k) (h2 : k ≤ j) :
      (𝔼).toCellScheme.gradedIndex (τ (u k)) = (W, k) :=
    hτg _ k (hu k h1 h2).1 h2
  have hθc (k) (h1 : 1 ≤ k) (h2 : k ≤ j) : ∀ d ∈ (𝔼).toCellScheme.below
      ((𝔼).toCellScheme.gradedIndex (mCopyFull hmix hU (u k) (hu k h1 h2).1 (h2.trans hjU))),
      θ k ((𝔼).rowAt (mCopyFull hmix hU (u k) (hu k h1 h2).1 (h2.trans hjU)) d) =
        min (P d) (P (mCopyFull hmix hU (u k) (hu k h1 h2).1 (h2.trans hjU))) := by
    rw [← mCpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hθ k h1 h2).2.2
  have hθcle (k) (h1 : 1 ≤ k) (h2 : k ≤ j) (x) :
      θ k x ≤ P (mCopyFull hmix hU (u k) (hu k h1 h2).1 (h2.trans hjU)) := by
    rw [← mCpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hθ k h1 h2).2.1 x
  have hmaxc (k) (h1 : 1 ≤ k) (h2 : k ≤ j) (w)
      (hw : T.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)) :
      P (mCopyFull hmix hU w hw (h2.trans hjU)) ≤
        P (mCopyFull hmix hU (u k) (hu k h1 h2).1 (h2.trans hjU)) := by
    rw [← mCpy_eq hU hw (h2.trans hjU), ← mCpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hu k h1 h2).2.2 w hw
  -- the values of the lift
  have hr_full (d) (hd : d ∈ (𝔼).toCellScheme.below (W, j))
      (v : Fin T.card) (hv : T.mirrorOrig (I.mixedFaces g) d = v) (k : ℕ)
      (hk : (𝔼).toCellScheme.grade d = k)
      (hgv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) :
      r d = P (mCpy hmix hU v) := by
    obtain ⟨h1, h2⟩ := hk ▸ hgY d hd
    have hdu : d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (τ (u k))) := by
      rw [hgiu k h1 h2, CellScheme.mem_below]
      exact ⟨hd.1, hk.le⟩
    rw [hrdef, hk, Scheme.rowAt_mirror_of_mem hdu, hτo, hv,
      decode_mCopyFull hU (hu k h1 h2).1 (h2.trans hjU) (hθc k h1 h2) hgv le_rfl,
      mCpy_eq hU hgv (h2.trans hjU)]
    exact min_eq_left (hmaxc k h1 h2 v hgv)
  have hr_att (e : Fin (I.attachment g).card) (k : ℕ)
      (hk : (I.attachment g).toCellScheme.grade e = k)
      (hem : (Fin.castAdd _ (att e) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below (W, j)) :
      r (Fin.castAdd _ (att e)) = θ k (T.rowAt (u k) (att e)) := by
    have hg : (𝔼).toCellScheme.grade (Fin.castAdd _ (att e)) = k :=
      (congrArg Prod.snd (hgiA e)).trans hk
    obtain ⟨h1, h2⟩ := hg ▸ hgY _ hem
    have hmem : (Fin.castAdd _ (att e) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (τ (u k))) := by
      rw [hgiu k h1 h2, CellScheme.mem_below]
      exact ⟨hem.1, hg.le⟩
    rw [hrdef, hg, Scheme.rowAt_mirror_of_mem hmem, hτo, Scheme.mirrorOrig_castAdd]
  -- copies and originals carry the same label
  have hsame (L : Fin (𝔼).card → Label.{u})
      (hL : (𝔼).rows.IsLawfulBelow (W, j) fun d ↦ L d)
      (v : Fin T.card) (k : ℕ)
      (hgv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hkj : k ≤ j)
      (z : Fin (𝔼).card) (hzY : z ∈ (𝔼).toCellScheme.below (W, j))
      (hz : T.mirrorOrig (I.mixedFaces g) z = v) :
      L z = L (τ v) := by
    have hcY : τ v ∈ (𝔼).toCellScheme.below (W, j) := by
      rw [CellScheme.mem_below, hτg v k hgv hkj]
      exact ⟨subset_rfl, hkj⟩
    refine Scheme.eq_of_mirrorOrig_eq hL (by rw [hz, hτo]) ?_ hcY
    exact hzY.1.trans (le_of_eq (congrArg Prod.fst (hτg v k hgv hkj)).symm)
  have hcfY (v : Fin T.card) (k : ℕ)
      (hgv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hkj : k ≤ j) :
      mCpy hmix hU v ∈ (𝔼).toCellScheme.below (U, j) := by
    rw [mCpy_eq hU hgv (hkj.trans hjU), CellScheme.mem_below, gradedIndex_mCopyFull]
    exact ⟨subset_rfl, hkj⟩
  have hcfo (v : Fin T.card) :
      T.mirrorOrig (I.mixedFaces g) (mCpy hmix hU v) = v := mirrorOrig_mCpy hU v
  -- the rows of the dominating cells
  have hρ (k) (h1 : 1 ≤ k) (h2 : k ≤ j) :
      (𝔼).rows.IsLawfulBelow (W, k) fun e ↦ (𝔼).rowAt (τ (u k)) e.1 :=
    Scheme.isLawfulBelow_rowAt (Scheme.isConsistent_mirror hcons) (hgiu k h1 h2)
  have hbelowk (d) (hd : d ∈ (𝔼).toCellScheme.below (W, j)) :
      d ∈ (𝔼).toCellScheme.below (W, (𝔼).toCellScheme.grade d) :=
    ⟨hd.1, le_rfl⟩
  -- the decoder at the top rung
  have hu1 : u 1 = lad top := (hu 1 le_rfl hj1).2.1 rfl
  have hθ1 : ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
      (mCopyLadder hmix hlad hU top)),
      θ 1 ((𝔼).rowAt (mCopyLadder hmix hlad hU top) d) =
        min (P d) (P (mCopyLadder hmix hlad hU top)) := by
    have h := (hθ 1 le_rfl hj1).2.2
    rw [hu1, mCpy_eq hU (hlad top) hU1] at h
    exact h
  -- the reading of a cell of the attachment through the dominating cell of its grade, capped at
  -- a cell of full scope, is the reading by that cell
  have hSC (K : ℕ) (hK1 : 1 ≤ K) (hKj : K ≤ j) (f : Fin T.card)
      (hgf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
      {θf : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
      (hθf_le : ∀ x, θf x ≤ P (mCopyFull hmix hU f hgf (hKj.trans hjU)))
      (hθf : ∀ d ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (mCopyFull hmix hU f hgf (hKj.trans hjU))),
        θf ((𝔼).rowAt (mCopyFull hmix hU f hgf (hKj.trans hjU)) d) =
          min (P d) (P (mCopyFull hmix hU f hgf (hKj.trans hjU))))
      (e : Fin (I.attachment g).card) (k : ℕ) (hek : (I.attachment g).toCellScheme.grade e = k)
      (hkK : k ≤ K) :
      min (θ k (T.rowAt (u k) (att e))) (P (mCopyFull hmix hU f hgf (hKj.trans hjU))) =
        θf (T.rowAt f (att e)) := by
    have hk1 : 1 ≤ k := by
      have := hpos (att e)
      rw [show T.toCellScheme.grade (att e) = (I.attachment g).toCellScheme.grade e from
        congrArg Prod.snd (hatt e)] at this
      omega
    rcases Nat.lt_or_ge k 2 with hk | hk2
    · have hk' : k = 1 := by omega
      subst hk'
      rw [hu1]
      exact min_decode_eq_decode_one_m hU hH hlad hrowLL hrowLA hone hread hK1 (hKj.trans hjU)
        hgf a (fun v ↦ ha v) hθf_mono hθf_le hθf hθ1 hek
    · exact min_decode_eq_decode_m hU hlad hagree htwin hk2 hkK (hKj.trans hjU) hgf
        (hu k hk1 (hkK.trans hKj)).1 (hmaxc k hk1 (hkK.trans hKj)) hθf_mono hθf_le hθf
        (hθc k hk1 (hkK.trans hKj)) hek
  refine ⟨fun d ↦ r d, ?_, fun d ↦ ?_, fun d ↦ ?_⟩
  · refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ?_⟩
    · -- order
      obtain ⟨h1, h2⟩ := hgY d hd
      have hvis := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ _ h1 h2)).1 d (hbelowk d hd)
      rw [hrdef]
      exact (hθ _ h1 h2).1.isSelfVisible_apply hvis (by simp)
    · -- locality
      obtain ⟨h1, h2⟩ := hgY s hs
      set K := (𝔼).toCellScheme.grade s with hKdef
      have hbs (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
          d.1 ∈ (𝔼).toCellScheme.below (W, j) :=
        CellScheme.Rows.mem_below_of_le d.2 hs
      have hdK (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
          (𝔼).toCellScheme.grade d.1 ≤ K := d.2.2
      rcases mirror_cell_cases_att (hmix := hmix) hcells s with ⟨f, hf, hgf⟩ | ⟨es, hes⟩
      · -- a cell of full scope or a copy: the decoder at the copy at `U` is the witness
        have hcf := mCpy_eq (hmix := hmix) hU hgf (h2.trans hjU)
        obtain ⟨θf, hθfw, hθfle, hθfr⟩ := Scheme.exists_cappedDecoder_below hP (hcfY f K hgf h2)
          (show (𝔼).toCellScheme.grade (mCpy hmix hU f) = K by
            rw [hcf]; exact congrArg Prod.snd (gradedIndex_mCopyFull hU _ _ _))
        rw [hcf] at hθfle hθfr
        have hrs : r s = P (mCopyFull hmix hU f hgf (h2.trans hjU)) := by
          rw [hr_full s hs f hf K rfl hgf, hcf]
        refine ⟨stepSuppressor K, θf, hθfw, fun d ↦ ?_⟩
        change min (r d.1) (r s) = min (θf ((𝔼).rows.row s d)) (stepSuppressor K
          ((𝔼).toCellScheme.grade d.1))
        rw [stepSuppressor_of_le (hdK d), min_top_right, ← Scheme.rowAt_of_mem d.2,
          Scheme.rowAt_mirror_of_mem d.2, hf, hrs]
        rcases mirror_cell_cases_att (hmix := hmix) hcells d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
        · rw [hv, hr_full d.1 (hbs d) v hv _ rfl hgv,
            decode_mCopyFull hU hgf (h2.trans hjU) hθfr hgv (hdK d)]
          exact congrArg₂ min (congrArg P (mCpy_eq hU hgv _)) rfl
        · have hek : (I.attachment g).toCellScheme.grade e = (𝔼).toCellScheme.grade d.1 := by
            rw [he]; exact (congrArg Prod.snd (hgiA e)).symm
          rw [he, hr_att e _ hek (he ▸ hbs d), Scheme.mirrorOrig_castAdd]
          exact hSC K h1 h2 f hgf hθfw.monotone hθfle hθfr e _ hek (hek ▸ hdK d)
      · -- a cell of the attachment: through the decoded row of the dominating cell
        have hsc : (𝔼).toCellScheme.scope s ⊆
            univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
            (𝔼).toCellScheme.scope s ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
          rw [hes, show (𝔼).toCellScheme.scope (Fin.castAdd _ (att es)) =
            (I.attachment g).toCellScheme.scope es from congrArg Prod.fst (hgiA es)]
          exact I.scope_attachment g es
        have hds (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
            ∃ e, d.1 = Fin.castAdd _ (att e) ∧ (I.attachment g).toCellScheme.grade e ≤ K := by
          obtain ⟨e, he⟩ := exists_att_of_scope (hmix := hmix) hcells d.1
            (hsc.imp (fun h ↦ d.2.1.trans h) fun h ↦ d.2.1.trans h)
          refine ⟨e, he, ?_⟩
          have := hdK d
          rw [he] at this
          exact (congrArg Prod.snd (hgiA e)).symm.trans_le this
        have hρd (e : Fin (I.attachment g).card)
            (hem : (Fin.castAdd _ (att e) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below (W, j))
            (hek : (I.attachment g).toCellScheme.grade e ≤ K) :
            (𝔼).rowAt (τ (u K)) (Fin.castAdd _ (att e)) = T.rowAt (u K) (att e) := by
          have hmem : (Fin.castAdd _ (att e) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below
              ((𝔼).toCellScheme.gradedIndex (τ (u K))) := by
            rw [hgiu K h1 h2, CellScheme.mem_below, hgiA]
            exact ⟨(congrArg Prod.fst (hgiA e)).symm.trans_le hem.1, hek⟩
          rw [Scheme.rowAt_mirror_of_mem hmem, hτo, Scheme.mirrorOrig_castAdd]
        have hrs : r s = θ K ((𝔼).rowAt (τ (u K)) s) := hrdef s
        have hclaim (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
            min (r d.1) (r s) = min (θ K ((𝔼).rowAt (τ (u K)) d.1))
              (θ K ((𝔼).rowAt (τ (u K)) s)) := by
          obtain ⟨e, he, hek⟩ := hds d
          rw [← hrs, he, hr_att e _ rfl (he ▸ hbs d), hρd e (he ▸ hbs d) hek]
          have h := hSC K h1 h2 (u K) (hu K h1 h2).1 (hθ K h1 h2).1.monotone (hθcle K h1 h2)
            (hθc K h1 h2) e _ rfl hek
          have hrsle : r s ≤ P (mCopyFull hmix hU (u K) (hu K h1 h2).1 (h2.trans hjU)) := by
            rw [hrs]; exact hθcle K h1 h2 _
          rw [← h, min_assoc, min_eq_right hrsle]
        have hlocρ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ K h1 h2)).2.1 s
          (hbelowk s hs)
        have hvisρ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ K h1 h2)).1 s
          (hbelowk s hs)
        have hfun : (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
            min (r d.1) (r s)) = fun d ↦ min (θ K ((𝔼).rowAt (τ (u K)) d.1))
              (θ K ((𝔼).rowAt (τ (u K)) s)) := funext hclaim
        change TransformsTo (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
          (𝔼).toCellScheme.grade d.1) ((𝔼).rows.row s) fun d ↦ min (r d.1) (r s)
        rw [hfun]
        -- the bottom pattern of the decoded row
        have hdich : (∀ d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s),
              θ K ((𝔼).rowAt (τ (u K)) d.1) = ⊥) ∨
            ∀ d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s),
              (θ K ((𝔼).rowAt (τ (u K)) d.1) = ⊥ ↔ (𝔼).rowAt (τ (u K)) d.1 = ⊥) := by
          rcases Nat.lt_or_ge K 2 with hK | hK2
          · have hK1 : K = 1 := by omega
            have huK : u K = lad top := by rw [hK1, hu1]
            have hθK : θ K = θ 1 := by rw [hK1]
            have he1 (e : Fin (I.attachment g).card)
                (hek : (I.attachment g).toCellScheme.grade e ≤ K) :
                (I.attachment g).toCellScheme.grade e = 1 := by
              have := hpos (att e)
              rw [show T.toCellScheme.grade (att e) = (I.attachment g).toCellScheme.grade e from
                congrArg Prod.snd (hatt e)] at this
              omega
            rcases decode_one_dichotomy_m hU hH hlad hrowLL hrowLA hP hj1 a ha hθ1 with
              hall | hiff
            · left
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd e (he ▸ hbs d) hek, huK, hθK]
              exact hall e (he1 e hek)
            · right
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd e (he ▸ hbs d) hek, huK, hθK]
              exact hiff e (he1 e hek)
          · rcases decode_controller_dichotomy_m hU hH hlad hrowLL hread hP hj1 hK2
                (h2.trans hjU) (hu K h1 h2).1 (hθ K h1 h2).1.map_bot (hθc K h1 h2) with
              hall | hiff
            · left
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd e (he ▸ hbs d) hek]
              exact hall e hek
            · right
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd e (he ▸ hbs d) hek]
              exact hiff e hek
        rcases hdich with hall | hiff
        · have hfun0 : (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
              min (θ K ((𝔼).rowAt (τ (u K)) d.1))
                (θ K ((𝔼).rowAt (τ (u K)) s))) = fun _ ↦ ⊥ :=
            funext fun d ↦ by rw [hall d, min_eq_left bot_le]
          rw [hfun0]
          exact TransformsTo.bot _ _
        · exact TransformsTo.map_of_bot_iff (K := K)
            (grade := fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
              (𝔼).toCellScheme.grade d.1)
            (E := (𝔼).rows.row s)
            (p := fun d ↦ (𝔼).rowAt (τ (u K)) d.1)
            (q := fun d ↦ (𝔼).rowAt (τ (u K)) d.1)
            (c := ⟨s, CellScheme.mem_below_gradedIndex _ s⟩) (fun d ↦ hdK d) le_rfl hvisρ hlocρ
            hvisρ hlocρ (hθ K h1 h2).1 hiff
    · -- availability
      obtain ⟨h1, h2⟩ := hgY t ht
      obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ _ h1 h2)
      obtain ⟨z, hz, hle⟩ := havail s t (hbelowk t ht) hst hg
      have hgz : (𝔼).toCellScheme.grade z = (𝔼).toCellScheme.grade t := congrArg Prod.snd hz
      refine ⟨z, hz, ?_⟩
      rw [hrdef s, hrdef z, hg, hgz]
      exact (hθ _ h1 h2).1.monotone hle
  · -- the observation of the ambient at the cap
    change min (r d) c = min (q d) c
    rw [← hQd d.1 d.2]
    obtain ⟨h1, h2⟩ := hgY d.1 d.2
    rcases mirror_cell_cases_att (hmix := hmix) hcells d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
    · rw [hr_full d.1 d.2 v hv _ rfl hgv, hsame Q hQ v _ hgv h2 d.1 d.2 hv,
        ← hsame Q hQ v _ hgv h2 _ (le_trans (hcfY v _ hgv h2) hXY) (hcfo v),
        hpq' _ (hcfY v _ hgv h2)]
    · set k := (I.attachment g).toCellScheme.grade e with hkdef
      have hdk : (𝔼).toCellScheme.grade d.1 = k := by
        rw [he]; exact congrArg Prod.snd (hgiA e)
      have hk1 : 1 ≤ k := hdk ▸ h1
      have hkj : k ≤ j := hdk ▸ h2
      obtain ⟨v, hv⟩ := exists_mshadow hrowLA hone hread hk1 (u k) (hu k hk1 hkj).1 hkdef.symm
      have hgl := hlad v
      have hrd : r d.1 = min (P (mCpy hmix hU (lad v))) (P (mCpy hmix hU (u k))) := by
        rw [he, hr_att e k rfl (he ▸ d.2), hv,
          decode_mCopyFull hU (hu k hk1 hkj).1 (hkj.trans hjU) (hθc k hk1 hkj) hgl hk1]
        exact congrArg₂ min (congrArg P (mCpy_eq hU hgl (hk1.trans (hkj.trans hjU))).symm)
          (congrArg P (mCpy_eq hU (hu k hk1 hkj).1 (hkj.trans hjU)).symm)
      rw [hrd]
      have hcuY : (τ (u k) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below (W, j) := by
        rw [CellScheme.mem_below, hgiu k hk1 hkj]; exact ⟨subset_rfl, hkj⟩
      have hdu : d.1 ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (τ (u k))) := by
        rw [hgiu k hk1 hkj, CellScheme.mem_below]
        exact ⟨d.2.1, hdk.le⟩
      have hτl : (𝔼).toCellScheme.gradedIndex (τ (lad v)) = (W, 1) :=
        hτg _ 1 hgl hj1
      have hlu : τ (lad v) ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (τ (u k))) := by
        rw [hgiu k hk1 hkj, CellScheme.mem_below, hτl]
        exact ⟨subset_rfl, hk1⟩
      have hdz := Scheme.min_eq_min_of_rowAt_eq hQ hcuY hdu hlu (by
        rw [Scheme.rowAt_mirror_of_mem hdu, Scheme.rowAt_mirror_of_mem hlu, hτo, hτo, he,
          Scheme.mirrorOrig_castAdd, hv])
      have hℓ : min (Q (τ (lad v))) c = min (P (mCpy hmix hU (lad v))) c := by
        rw [← hsame Q hQ _ 1 hgl hj1 _ (le_trans (hcfY _ 1 hgl hj1) hXY) (hcfo _),
          hpq' _ (hcfY _ 1 hgl hj1)]
      have hzM : min (Q (τ (u k))) c = min (P (mCpy hmix hU (u k))) c := by
        rw [← hsame Q hQ _ k (hu k hk1 hkj).1 hkj _
            (le_trans (hcfY _ k (hu k hk1 hkj).1 hkj) hXY) (hcfo _),
          hpq' _ (hcfY _ k (hu k hk1 hkj).1 hkj)]
      obtain ⟨-, -, havailQ⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hQ
      obtain ⟨z, hz, hle⟩ := havailQ d.1 _ hcuY
        (subset_trans d.2.1 (le_of_eq (congrArg Prod.fst (hgiu k hk1 hkj)).symm))
        (hdk.trans (congrArg Prod.snd (hgiu k hk1 hkj)).symm)
      have hzW := hz.trans (hgiu k hk1 hkj)
      have hzY : z ∈ (𝔼).toCellScheme.below (W, j) := by
        rw [CellScheme.mem_below, hzW]; exact ⟨subset_rfl, hkj⟩
      obtain ⟨w', hw'o, hgw'⟩ : ∃ w', T.mirrorOrig (I.mixedFaces g) z = w' ∧
          T.toCellScheme.gradedIndex w' = ((univ : Finset (Fin (m + 2))), k) := by
        rcases mirror_cell_cases_att (hmix := hmix) hcells z with ⟨w', hw'o, hgw'⟩ | ⟨ez, hez⟩
        · exact ⟨w', hw'o, hgw'.trans (congrArg _ (congrArg Prod.snd hzW))⟩
        · exfalso
          obtain ⟨-, -, hc, hd⟩ := (I.mem_mixedFaces g).mp hU
          have hsz : U ⊆ (𝔼).toCellScheme.scope z :=
            hUW.trans (le_of_eq (congrArg Prod.fst hzW).symm)
          rw [hez, show (𝔼).toCellScheme.scope (Fin.castAdd _ (att ez)) =
            (I.attachment g).toCellScheme.scope ez from congrArg Prod.fst (hgiA ez)] at hsz
          exact (I.scope_attachment g ez).elim (fun h ↦ hc (hsz.trans h))
            fun h ↦ hd (hsz.trans h)
      have hwM : min (Q z) c ≤ min (P (mCpy hmix hU (u k))) c := by
        rw [hsame Q hQ _ k hgw' hkj z hzY hw'o,
          ← hsame Q hQ _ k hgw' hkj _ (le_trans (hcfY _ k hgw' hkj) hXY) (hcfo _),
          hpq' _ (hcfY _ k hgw' hkj)]
        exact min_le_min_right _ ((hu k hk1 hkj).2.2 w' hgw')
      exact Label.min_min_eq_of_reader hdz hℓ hzM hle hwM
  · -- the prescription below `(U, j)`
    change r d.1 = p d
    have hdY : d.1 ∈ (𝔼).toCellScheme.below (W, j) := le_trans d.2 hXY
    obtain ⟨h1, h2⟩ := hgY d.1 hdY
    rw [← hPd d.1 d.2]
    rcases mirror_cell_cases_att (hmix := hmix) hcells d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
    · rw [hr_full d.1 hdY v hv _ rfl hgv]
      refine (Scheme.eq_of_mirrorOrig_eq hP (by rw [hv, hcfo v]) ?_ (hcfY v _ hgv h2)).symm
      rw [mCpy_eq hU hgv (h2.trans hjU)]
      exact d.2.1.trans (le_of_eq (congrArg Prod.fst (gradedIndex_mCopyFull hU v hgv _)).symm)
    · set k := (I.attachment g).toCellScheme.grade e with hkdef
      have hdk : (𝔼).toCellScheme.grade d.1 = k := by
        rw [he]; exact congrArg Prod.snd (hgiA e)
      have hk1 : 1 ≤ k := hdk ▸ h1
      have hkj : k ≤ j := hdk ▸ h2
      have hes : (I.attachment g).toCellScheme.scope e ⊆ U := by
        have h := d.2.1
        rw [he] at h
        exact (congrArg Prod.fst (hgiA e)).symm.trans_le h
      have hmem : (Fin.castAdd _ (att e) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex
            (mCopyFull hmix hU (u k) (hu k hk1 hkj).1 (hkj.trans hjU))) := by
        rw [CellScheme.mem_below, gradedIndex_mCopyFull, hgiA]
        exact ⟨hes, le_rfl⟩
      have hrow : (𝔼).rowAt (mCopyFull hmix hU (u k) (hu k hk1 hkj).1 (hkj.trans hjU))
          (Fin.castAdd _ (att e)) = T.rowAt (u k) (att e) := by
        rw [Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_mCopyFull, Scheme.mirrorOrig_castAdd]
      rw [he, hr_att e k rfl (he ▸ hdY), ← hrow, hθc k hk1 hkj _ hmem]
      exact min_eq_left (le_max_mCopy hU hP hkj (hkj.trans hjU) (hu k hk1 hkj).1
        (hmaxc k hk1 hkj) (he ▸ d.2) (congrArg Prod.snd (hgiA e)))


/-- **The lift from a mixed face into the full face** of a mirrored scheme over the attachment
(the cells of full scope read at themselves). -/
theorem cappedLift_mirror_mixed_univ (hH : 0 < H)
    (hcons : T.rows.IsConsistent) (hpos : ∀ d, 1 ≤ T.toCellScheme.grade d)
    (hatt : ∀ e, T.toCellScheme.gradedIndex (att e) = (I.attachment g).toCellScheme.gradedIndex e)
    (hcells : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p) (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 2))), 1) →
      ∃ p, x = lad p)
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    (hagree : ∀ f u K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      T.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k → ∃ v,
        T.rowAt u (lad v) = T.rowAt u (att e) ∧
        min (T.rowAt f (lad v)) (T.rowAt f u) = min (T.rowAt f (att e)) (T.rowAt f u))
    (htwin : ∀ f K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      2 ≤ k → k ≤ K → ∀ e, (I.attachment g).toCellScheme.grade e = k →
      ∃ et, T.toCellScheme.gradedIndex et = ((univ : Finset (Fin (m + 2))), k) ∧
        T.rowAt f (att e) ≤ T.rowAt f et)
    (hU : U ∈ I.mixedFaces g) {j : ℕ}
    (hexist : ∀ k, 2 ≤ k → k ≤ j → ∃ f, T.toCellScheme.gradedIndex f =
      ((univ : Finset (Fin (m + 2))), k))
    (hj1 : 1 ≤ j) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_mirror_mixed_face hH hcons hpos hatt hcells hlad hrowLL hrowLA hone hread hagree
    htwin hU (subset_univ _) (Fin.castAdd _) (fun v ↦ Scheme.mirrorOrig_castAdd _ _ v)
    (fun v _ hv _ ↦ (Scheme.gradedIndex_mirror_castAdd (hmix := hmix) v).trans hv) hexist hj1 hjU

/-- **The lift between mixed faces at a grade** of a mirrored scheme over the attachment (the cells
of full scope read at their copies at the larger face). -/
theorem cappedLift_mirror_mixed_mixed (hH : 0 < H)
    (hcons : T.rows.IsConsistent) (hpos : ∀ d, 1 ≤ T.toCellScheme.grade d)
    (hatt : ∀ e, T.toCellScheme.gradedIndex (att e) = (I.attachment g).toCellScheme.gradedIndex e)
    (hcells : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p) (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 2))), 1) →
      ∃ p, x = lad p)
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    (hagree : ∀ f u K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      T.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k → ∃ v,
        T.rowAt u (lad v) = T.rowAt u (att e) ∧
        min (T.rowAt f (lad v)) (T.rowAt f u) = min (T.rowAt f (att e)) (T.rowAt f u))
    (htwin : ∀ f K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) →
      2 ≤ k → k ≤ K → ∀ e, (I.attachment g).toCellScheme.grade e = k →
      ∃ et, T.toCellScheme.gradedIndex et = ((univ : Finset (Fin (m + 2))), k) ∧
        T.rowAt f (att e) ≤ T.rowAt f et)
    (hU : U ∈ I.mixedFaces g) {V : Finset (Fin (m + 2))} (hV : V ∈ I.mixedFaces g)
    (hUV : U ⊆ V) {j : ℕ}
    (hexist : ∀ k, 2 ≤ k → k ≤ j → ∃ f, T.toCellScheme.gradedIndex f =
      ((univ : Finset (Fin (m + 2))), k))
    (hj1 : 1 ≤ j) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (V, j)) ⟨hUV, le_rfl⟩ :=
  cappedLift_mirror_mixed_face hH hcons hpos hatt hcells hlad hrowLL hrowLA hone hread hagree
    htwin hU hUV (mCpy hmix hV) (mirrorOrig_mCpy hV)
    (fun _ _ hv hk ↦ by
      rw [mCpy_eq hV hv (hk.trans (hjU.trans (card_le_card hUV)))]
      exact gradedIndex_mCopyFull hV _ _ _) hexist hj1 hjU

end Seed

end VaughtConjecture

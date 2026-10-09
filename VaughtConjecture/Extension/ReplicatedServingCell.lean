/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedRankAgreement
import VaughtConjecture.Extension.LadderTowerContextLiftCoding

/-!
# Serving cells of the replicated scheme at the full faces

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap).

**Every state of the catalogue has its cell** (`Scheme.exists_layerTower_cell_of_mem`,
`Seed.exists_cell_of_mem_towerCat`): for a state `R` of the catalogue at a grade `2 ≤ k ≤ m + 1`,
some cell of the replicated scheme at `(univ, k)` reads `R` at the cells of the attachment of grade
at most `k` and the positive table of `R` at the ladder index of its own rank member at every
ladder point.  Conversely every cell at `(univ, k)` is such a cell
(`Seed.exists_state_of_cell`).

**No mixed cell** (`Seed.rowAt_rung_of_state`, `Seed.lt_rankCut_of_rung_agree`).  A cell of a
state `R` reads the rung `i` of a member `b` as the positive table of `R` at
`min (rankCut (a_R, b)) (i + 1)`: its ladder reading goes through the rank member `a_R` of its own
state, and through `b` only up to the cut of the two rank vectors, taken over all the cells of the
attachment.  If the readings of two rungs of `b` by such a cell, under any map and capped at `c`,
match an ambient that separates the two rungs at `c`, the cut exceeds the lower rung.  So a cell
whose ladder reading is that of the ambient's member `b` capped at `c` below the first rank where
the table of `b` reaches `c` has a state whose rank vector agrees with `b` over all the cells, up
to that rank: there is no cell reading the ladder through `b` and the attachment through an
unrelated state, and no restriction of the agreement to the cells of grade one inside the
replicated scheme.  The ambient's own controllers above the cap are such cells
(`Seed.lt_rankCut_of_ambient`): their states agree with `b` over all the cells up to the
separated rung.

**The pin does not apply to serving cells.**  `Seed.not_exists_coded_rankAgree` needs the state
read from `R` to be lawful at every cell.  A serving cell asks only that its decoded reading of the
attachment be the prescription at the cells of grade at most `k`; the values of `R` above the grade
are those of a lawful state of the catalogue, and the decoder, a witness bounded by `k`, may lower
their visibility.  So the configuration of `Seed.not_exists_coded_rankAgree` constrains a serving
state only through its own lawfulness.

**The serving cell at a grade** (`Seed.ServingCellAt`): a cell `u` at `(univ, k)` and a witness `σ`
bounded by `k` reading the attachment cells of grade at most `k` as `P` capped at `x` and the ladder
as the ambient capped at `c`.  **The serving state** (`Seed.ServingStateAt`, open): a state of the
catalogue at `k` and such a witness, on the writing of the state.  The serving state gives the
serving cell (`Seed.servingCellAt_of_servingStateAt`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} {σ : Type v} {B : LayerTower.{u} n σ 0} {C : ℕ → Finset σ}
  {G : ℕ → Finset Label.{u}}

/-- **Every state of the catalogue has its cell**: for a state `R` of `C (k + 2)`, at every height
`K ≥ k + 1` some cell at `(univ, k + 2)` reads the writing of `R` at every cell of the base of
grade at most `k + 2`. -/
theorem exists_layerTower_cell_of_mem (k : ℕ) {R : σ} (hR : R ∈ C (k + 2)) :
    ∀ K, k + 1 ≤ K → ∃ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) ∧
      ∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
        (layerTower B C G K).S.rowAt u (layerTowerEmb K t) = B.v R t := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, hi⟩ := exists_layerEntry_eq (C := T.entries (C (k + 2)))
      (mem_image_of_mem T.v hR)
    refine ⟨Fin.natAdd _ i, ?_, fun t ht ↦ ?_⟩
    · change (T.S.appendFullCellsScheme (k + 2) _).gradedIndex (Fin.natAdd _ i) = _
      rw [appendFullCellsScheme_gradedIndex_natAdd]
    · have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
        have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
        change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
        omega
      change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
        T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb k t)) = _
      rw [rowAt_catalogueLayer_castAdd i hgt, hi]
      exact layerTower_v_emb R t k
  | succ K hK ih =>
    set T := layerTower B C G K with hT
    obtain ⟨u, hu, hrow⟩ := ih
    refine ⟨Fin.castAdd _ u, ?_, fun t ht ↦ ?_⟩
    · change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ u) = _
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact hu
    · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
        T.not_le).rowAt (Fin.castAdd _ u) (Fin.castAdd _ (layerTowerEmb K t)) = _
      rw [rowAt_appendFullCells_castAdd]
      exact hrow t ht

namespace LadderBaseData

variable {B : LadderBaseData.{u} n} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin B.S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **Every lawful state of the catalogue has its cell in the ladder tower**, reading the state on
the base cells of grade at most its grade and its positive table at the base indices of its rank
member on the ladder. -/
theorem exists_cell_of_mem_towerCat (hcard : B.S.card ≤ H) (k K : ℕ) (hK : k + 1 ≤ K)
    {R : Fin B.S.card → Label.{u}} (hRC : R ∈ B.towerCat Γ A (k + 2)) :
    ∃ (u : Fin (B.ladderTower H Γ A B' K).S.card) (hR : B.S.rows.IsLawful R),
      (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin n)), k + 2) ∧
      (∀ d : Fin B.S.card, B.S.toCellScheme.grade d ≤ k + 2 →
        (B.ladderTower H Γ A B' K).S.rowAt u (B.towerEmb K (Fin.castAdd _ d)) = R d) ∧
      ∀ p, (B.ladderTower H Γ A B' K).S.rowAt u
          (B.towerEmb K (Fin.natAdd _ (ladderEquiv _ _ H p))) =
        posTable R (baseIndex H (rankProf B.S H)
          (RankMember.ofLawful B.wf hcard hR)
          (Fin.natAdd _ (ladderEquiv _ _ H p))) := by
  obtain ⟨u, hu, hrow⟩ := exists_layerTower_cell_of_mem (B := B.towerBase H)
    (C := B.towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) k hRC K hK
  have hRl := (mem_towerCat.mp hRC).2.1
  refine ⟨u, hRl, hu, fun d hd ↦ ?_, fun p ↦ ?_⟩
  · have h := hrow (Fin.castAdd _ d) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k + 2
      rw [appendFullCellsScheme_grade_castAdd]; exact hd)
    exact h.trans (stateExt_castAdd hRl hcard d)
  · have h := hrow (Fin.natAdd _ (ladderEquiv _ _ H p)) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.natAdd _ _) ≤ k + 2
      rw [appendFullCellsScheme_grade_natAdd]; omega)
    exact h.trans
      (stateExt_of_grade_one hRl hcard _ (appendFullCellsScheme_grade_natAdd _ _ _ _))

end LadderBaseData

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- **The reading of a cell of a state**: a cell of the replicated scheme which is the cell of a
lawful state `R` of the tower reads `R` at the attachment cells of grade at most its grade and the
positive table of `R` at the ladder index of its own rank member at every ladder point. -/
def ReadsState (hcard : (I.attachmentBase g).S.card ≤ H) (u : Fin (𝔼).card) (k : ℕ)
    (R : Fin (I.attachment g).card → Label.{u}) (hR : (I.attachment g).rows.IsLawful R) : Prop :=
  (∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
    (𝔼).rowAt u (I.attachEmb g H Γ A B' a) = R a) ∧
  ∀ p, (𝔼).rowAt u (ladderCellE H Γ A B' p) =
    posTable R (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
      (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
      (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR) p)

/-- The reading of a cell of the tower in the replicated scheme, from its reading in the tower. -/
theorem readsState_castAdd (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (u : Fin (I.attachTower g H Γ A B').card) {R : Fin (I.attachment g).card → Label.{u}}
    (hR : (I.attachment g).rows.IsLawful R)
    (hA : ∀ d, (I.attachmentBase g).S.toCellScheme.grade d ≤ k →
      (I.attachTower g H Γ A B').rowAt u ((I.attachmentBase g).towerEmb m (Fin.castAdd _ d)) =
        R d)
    (hL : ∀ p, (I.attachTower g H Γ A B').rowAt u
        ((I.attachmentBase g).towerEmb m (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))) =
      posTable R (Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H)
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR)
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p)))) :
    ReadsState hcard (Fin.castAdd _ u) k R hR := by
  refine ⟨fun a ha ↦ (Scheme.rowAt_mirror_castAdd _ _).trans (hA a ha), fun p ↦ ?_⟩
  refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hL p).trans ?_)
  rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]

/-- **Every state of the catalogue at a grade `2 ≤ k ≤ m + 1` has its cell in the replicated
scheme.** -/
theorem exists_cell_of_mem_towerCat (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) {R : Fin (I.attachment g).card → Label.{u}}
    (hRC : R ∈ (I.attachmentBase g).towerCat Γ A k) :
    ∃ (u : Fin (𝔼).card) (hR : (I.attachment g).rows.IsLawful R),
      (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) ∧
        ReadsState hcard u k R hR := by
  obtain ⟨u, hR, hu, hA, hL⟩ := Scheme.LadderBaseData.exists_cell_of_mem_towerCat
    (B := I.attachmentBase g) (Γ := Γ) (A := A) (B' := B') hcard (k - 2) m (by omega)
    (R := R) (by rw [show k - 2 + 2 = k by omega]; exact hRC)
  refine ⟨Fin.castAdd _ u, hR, (Scheme.gradedIndex_mirror_castAdd u).trans
    (hu.trans (by rw [show k - 2 + 2 = k by omega])), readsState_castAdd hcard u hR
    (fun d hd ↦ hA d (by omega)) hL⟩

/-- **Every cell at `(univ, k)`, `2 ≤ k ≤ m + 1`, is the cell of a state of the catalogue.** -/
theorem exists_state_of_cell (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) {u : Fin (𝔼).card}
    (hu : (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k)) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A k, ∃ hR : (I.attachment g).rows.IsLawful R,
      ReadsState hcard u k R hR := by
  obtain ⟨u, rfl⟩ : ∃ u' : Fin (I.attachTower g H Γ A B').card, u = Fin.castAdd _ u' := by
    induction u using Fin.addCases with
    | left u => exact ⟨u, rfl⟩
    | right jj =>
      exfalso
      exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd jj)).2.1 (congrArg Prod.fst hu)
  have hu' : (I.attachTower g H Γ A B').toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), k - 2 + 2) := by
    rw [show k - 2 + 2 = k by omega]
    exact (Scheme.gradedIndex_mirror_castAdd u).symm.trans hu
  obtain ⟨R, hRC, hR, hA, hL⟩ := Scheme.LadderBaseData.exists_controller_ladderTower
    (B := I.attachmentBase g) (A := A) (Γ := Γ) (B' := B') hcard (k - 2) m (by omega) u hu'
  exact ⟨R, by rw [show k - 2 + 2 = k by omega] at hRC; exact hRC, hR,
    readsState_castAdd hcard u hR (fun d hd ↦ hA d (by omega)) hL⟩

/-- **The rungs read by the cell of a state**: the rung `i` of a member `b` is read as the
positive table of the state at the smaller of the cut of its rank member with `b` and `i + 1`. -/
theorem rowAt_rung_of_state (hcard : (I.attachmentBase g).S.card ≤ H) {u : Fin (𝔼).card}
    {k : ℕ} {R : Fin (I.attachment g).card → Label.{u}} {hR : (I.attachment g).rows.IsLawful R}
    (h : ReadsState hcard u k R hR) (b : Scheme.RankMember (I.attachmentBase g).S H)
    (i : Fin H) :
    (𝔼).rowAt u (ladderCellE H Γ A B' (b, Sum.inl i)) =
      posTable R (min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1)) :=
  h.2 _

/-- **What a matching ladder reading forces**: if the readings of the rungs `i` and `i'` of a
member `b` by the cell of a state `R`, under a map `σ` and capped at `c`, are those of an ambient
`q` capped at `c`, and `q` separates the two rungs at `c`, then the cut of the rank member of `R`
with `b` exceeds `i + 1` or `i' + 1`: the rank vectors agree over all the cells of the attachment
beyond the lower rung. -/
theorem lt_rankCut_of_rung_agree (hcard : (I.attachmentBase g).S.card ≤ H) {u : Fin (𝔼).card}
    {k : ℕ} {R : Fin (I.attachment g).card → Label.{u}} {hR : (I.attachment g).rows.IsLawful R}
    (h : ReadsState hcard u k R hR) {σ : Label.{u} → Label.{u}} {c : Label.{u}}
    {q : Fin (𝔼).card → Label.{u}} (b : Scheme.RankMember (I.attachmentBase g).S H)
    {i i' : Fin H}
    (hi : min (σ ((𝔼).rowAt u (ladderCellE H Γ A B' (b, Sum.inl i)))) c =
      min (q (ladderCellE H Γ A B' (b, Sum.inl i))) c)
    (hi' : min (σ ((𝔼).rowAt u (ladderCellE H Γ A B' (b, Sum.inl i')))) c =
      min (q (ladderCellE H Γ A B' (b, Sum.inl i'))) c)
    (hne : min (q (ladderCellE H Γ A B' (b, Sum.inl i))) c ≠
      min (q (ladderCellE H Γ A B' (b, Sum.inl i'))) c) :
    (i : ℕ) + 1 < rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b) ∨
      (i' : ℕ) + 1 < rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b) := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hi, ← hi', rowAt_rung_of_state hcard h, rowAt_rung_of_state hcard h,
    min_eq_left hcon.1, min_eq_left hcon.2]

/-- **The ambient's controllers read the ladder through the ambient's member**: for an ambient `q`
lawful below `(univ, j)`, a cell `u` at `(univ, k)`, `2 ≤ k ≤ min j (m + 1)`, with `c ≤ q u`, and
two rungs of a member `b` that `q` separates at `c`, the state of `u` has a rank vector whose cut
with `b` exceeds the lower rung: the twins force the agreement over all the cells of the
attachment. -/
theorem lt_rankCut_of_ambient (hcard : (I.attachmentBase g).S.card ≤ H) {j k : ℕ} (hk2 : 2 ≤ k)
    (hkj : k ≤ j) (hkm : k ≤ m + 1) {q : Fin (𝔼).card → Label.{u}}
    (hq : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun d ↦ q d)
    {u : Fin (𝔼).card} (hu : (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    {c : Label.{u}} (hcu : c ≤ q u) (b : Scheme.RankMember (I.attachmentBase g).S H)
    {i i' : Fin H}
    (hne : min (q (ladderCellE H Γ A B' (b, Sum.inl i))) c ≠
      min (q (ladderCellE H Γ A B' (b, Sum.inl i'))) c) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A k, ∃ hR : (I.attachment g).rows.IsLawful R,
      ReadsState hcard u k R hR ∧
      ((i : ℕ) + 1 < rankCut H (Scheme.rankProf (I.attachmentBase g).S H
          (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
            (Scheme.rankProf (I.attachmentBase g).S H b) ∨
        (i' : ℕ) + 1 < rankCut H (Scheme.rankProf (I.attachmentBase g).S H
          (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
            (Scheme.rankProf (I.attachmentBase g).S H b)) := by
  obtain ⟨R, hRC, hR, hread⟩ := exists_state_of_cell (B' := B') hcard hk2 hkm hu
  have huY : u ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hu]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨θ, -, -, hθ⟩ := Scheme.exists_cappedDecoder_below hq huY (congrArg Prod.snd hu)
  have hagree (p : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      min (θ ((𝔼).rowAt u (ladderCellE H Γ A B' p))) c =
        min (q (ladderCellE H Γ A B' p)) c := by
    rw [hθ _ (by rw [hu]; exact ladderCellE_mem_below (by omega) p), min_assoc,
      min_eq_right hcu]
  exact ⟨R, hRC, hR, hread, lt_rankCut_of_rung_agree hcard hread b (hagree _) (hagree _) hne⟩

/-- **The serving cell at the grade `k`** for a prescription `P`, an ambient `q`, a cap `c` and a
label `x`: a cell `u` at `(univ, k)` and a witness `σ` bounded by `k` reading the attachment cells
of grade at most `k` as `P` capped at `x`, and every ladder point as `q` capped at `c`. -/
def ServingCellAt (k : ℕ) (P : Fin (I.attachment g).card → Label.{u})
    (q : Fin (𝔼).card → Label.{u}) (c x : Label.{u}) : Prop :=
  ∃ u : Fin (𝔼).card, (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) ∧
    ∃ σ : Label.{u} → Label.{u}, IsWitness (stepSuppressor k) σ ∧
      (∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
        σ ((𝔼).rowAt u (I.attachEmb g H Γ A B' a)) = min (P a) x) ∧
      ∀ p, min (σ ((𝔼).rowAt u (ladderCellE H Γ A B' p))) c =
        min (q (ladderCellE H Γ A B' p)) c

/-- **The serving state at the grade `k`** (open): a state `R` of the catalogue at `k` and a
witness `σ` bounded by `k` reading `R` as `P` capped at `x` at the cells of grade at most `k`, and
the positive table of `R` at the ladder index of its rank member as `q` capped at `c` at every
ladder point. -/
def ServingStateAt (hcard : (I.attachmentBase g).S.card ≤ H) (k : ℕ)
    (P : Fin (I.attachment g).card → Label.{u}) (q : Fin (𝔼).card → Label.{u})
    (c x : Label.{u}) : Prop :=
  ∃ R ∈ (I.attachmentBase g).towerCat Γ A k, ∃ hR : (I.attachment g).rows.IsLawful R,
    ∃ σ : Label.{u} → Label.{u}, IsWitness (stepSuppressor k) σ ∧
      (∀ a, (I.attachment g).toCellScheme.grade a ≤ k → σ (R a) = min (P a) x) ∧
      ∀ p, min (σ (posTable R (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
          (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR) p))) c =
        min (q (ladderCellE H Γ A B' p)) c

/-- **The serving state gives the serving cell**: its cell in the replicated scheme. -/
theorem servingCellAt_of_servingStateAt (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) {P : Fin (I.attachment g).card → Label.{u}}
    {q : Fin (𝔼).card → Label.{u}} {c x : Label.{u}}
    (h : ServingStateAt hcard k P q c x) : ServingCellAt (H := H) (Γ := Γ) (A := A) (B' := B')
      k P q c x := by
  obtain ⟨R, hRC, hR, σ, hσ, hdec, hlad⟩ := h
  obtain ⟨u, hR', hu, hread⟩ := exists_cell_of_mem_towerCat (B' := B') hcard hk2 hkm hRC
  refine ⟨u, hu, σ, hσ, fun a ha ↦ by rw [hread.1 a ha]; exact hdec a ha, fun p ↦ ?_⟩
  rw [hread.2 p]
  exact hlad p

end Seed

end VaughtConjecture

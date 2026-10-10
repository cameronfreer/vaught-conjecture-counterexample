/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedCompletion
import VaughtConjecture.Continuation.GrowthLadderRecognition
import VaughtConjecture.MainTheorem.GrowthCarrierExistence

/-!
# The ladder growth carrier over the replicated scheme

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The completion of the replicated scheme over the attachment (`Seed.replicatedCompletion`) is a
growth carrier with the context `I.left` and the donor `d` as literal faces
(`GrowthCarrier.ofExtension`).  Along the context and the donor faces its cells are the cells of
the attachment (`Seed.cellMap_replicatedCompletion`).  Its cells of full scope below the apex are
the cells of full scope of the ladder tower over the attachment (the copies have mixed scope), so
the controllers of the tower are its controllers: every cell of full scope at the threshold reads
an admitted state of the attachment on the context and donor cells and its positive table on the
ladder (`Seed.exists_replicatedCarrier`, a ladder carrier in the sense of
`GrowthCarrier.recognizes_of_ladder`).  The only inputs are the bountifulness of the replicated
scheme and a lawful labelling extending the labels of the attachment.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

The completion of [Kni26, Definition 4.3.14]; the controllers of the growth step are those of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}
  {d : StageType.{u} α (n + 1)}
  {H : ℕ} {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
  {B' : ℕ} (hα : Order.IsSuccPrelimit α)
  (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
  {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
  (hq : (I.replicated g H Γ A B').rows.IsLawful q)

/-- **Along a proper face whose visible cells are cells of the attachment, the cells of the
completion are those of the attachment**, in their order. -/
theorem cellMap_replicatedCompletion {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin (I.replicated g H Γ A B').card,
      ((I.replicated g H Γ A B').toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f →
        z ∈ Set.range (I.attachEmb g H Γ A B'))
    {i : Fin ((I.attachment g).comap f).card}
    {j : Fin ((replicatedCompletion hα hL hq).toScheme.comap f).card} (hij : (i : ℕ) = j) :
    (replicatedCompletion hα hL hq).toScheme.cellMap f j =
      (I.attachEmb g H Γ A B' ((I.attachment g).cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range f (S := I.attachment g)
    (T := (replicatedCompletion hα hL hq).toScheme)
    (φ := fun c ↦ (I.attachEmb g H Γ A B' c).castSucc)
    (fun a b hab ↦ Fin.castSucc_lt_castSucc_iff.mpr (strictMono_attachEmb hab)) (fun c ↦ ?_)
    (fun z hz ↦ ?_) hij
  · change ((I.replicated g H Γ A B').appendFullCellScheme (m + 2)).scope
      (I.attachEmb g H Γ A B' c).castSucc = _
    rw [Scheme.appendFullCellScheme_scope_castSucc, scope_attachEmb]
  · change Fin ((I.replicated g H Γ A B').card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      exfalso
      change (((I.replicated g H Γ A B').appendFullCellScheme (m + 2)).scope (Fin.last _) :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_last, coe_univ] at hz
      exact hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ := hz (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
    | cast z =>
      change (((I.replicated g H Γ A B').appendFullCellScheme (m + 2)).scope z.castSucc :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
      obtain ⟨c, rfl⟩ := hvis z hz
      exact ⟨c, rfl⟩

/-- The completion reads the cells of the replicated scheme as the replicated scheme does. -/
theorem rowAt_replicatedCompletion_castSucc (z x : Fin (I.replicated g H Γ A B').card) :
    (replicatedCompletion hα hL hq).toScheme.rowAt z.castSucc x.castSucc =
      (I.replicated g H Γ A B').rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := hL.not_le) z x

/-- The cells of the replicated scheme keep their graded indices in the completion. -/
theorem gradedIndex_replicatedCompletion_castSucc (z : Fin (I.replicated g H Γ A B').card) :
    (replicatedCompletion hα hL hq).toCellScheme.gradedIndex z.castSucc =
      (I.replicated g H Γ A B').toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has the full grade. -/
theorem gradedIndex_replicatedCompletion_last :
    (replicatedCompletion hα hL hq).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

variable (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

include hα in
/-- **The ladder growth carrier over the replicated scheme**: at a stage that is zero or a limit,
for requests `Q` on the donor with threshold at least `2`, a height `H ≥ 1` at least the number of
cells of the attachment, values of the states in a finite set `Γ` containing `⊥`, below the top of
the grid at the grade `2` and below `ω ^ 2`, if the replicated scheme with the admission predicate
of `Q` is bountiful and carries a lawful labelling extending the labels of the attachment, then
its completion is a growth carrier with the context `I.left` and the donor `d` as literal faces, a
field ladder of height `H`, and every cell of full scope at the threshold a ladder controller. -/
theorem exists_replicatedCarrier (Q : GrowthRequests I.left d.toScheme)
    (hN : 2 ≤ Q.threshold) (hH : 0 < H) (hcard : (I.attachment g).card ≤ H) (hΓ0 : ⊥ ∈ Γ)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hAe : A = I.attachAdmits g hd Q)
    (hbount : (I.replicated g H Γ A B').rows.IsBountiful)
    (hlab : ∃ q : Fin (I.replicated g H Γ A B').card → Label.{u},
      (I.replicated g H Γ A B').rows.IsLawful q ∧
        ∀ c, q (I.attachEmb g H Γ A B' c) = (I.attachmentType g).label c) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
        (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H, 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F := by
  classical
  subst hAe
  set A := I.attachAdmits g hd Q with hA
  set Bd := I.attachmentBase g with hBd
  obtain ⟨q, hq, hqe⟩ := hlab
  have hL := isLegalBelowFullGrade_replicated hH hcard hΓ0 hΓ hΓω (I.attachAdmits_succ g hd Q)
    (I.attachAdmits_bot g hd Q) hbount
  let G := GrowthCarrier.ofExtension (isLegal_replicatedCompletion hα hL hq)
    (restrictFace_left_replicatedCompletion hα hL hq hqe)
    (restrictFace_donor_replicatedCompletion hd hα hL hq hqe)
  set T := Bd.ladderTower H Γ A B' m with hT
  set N := Q.threshold with hNdef
  have hNm : N ≤ m + 1 := by
    have h1 := I.left.isWellFormed.isWellFormed.grade_le_card Q.cap
    have h2 : #(I.left.toCellScheme.scope Q.cap) ≤ m + 1 :=
      (card_le_univ _).trans (by simp)
    exact h1.trans h2
  -- the cells of the base in the completion
  let emb : Fin (Bd.ladderBase H).card → Fin G.scheme.card := fun t ↦
    Fin.castSucc (Fin.castAdd _ (Bd.towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m t))
  have hgi (t : Fin (Bd.ladderBase H).card) :
      G.scheme.toCellScheme.gradedIndex (emb t) = (Bd.ladderBase H).toCellScheme.gradedIndex t :=
    (gradedIndex_replicatedCompletion_castSucc hα hL hq _).trans
      ((Scheme.gradedIndex_mirror_castAdd _).trans
        (Scheme.gradedIndex_layerTowerEmb (B := Bd.towerBase H) (C := Bd.towerCat Γ A)
          (G := fun k ↦ Scheme.heightSet Γ B' k) t m))
  have hrowB (z t : Fin (Bd.ladderBase H).card) :
      G.scheme.rowAt (emb z) (emb t) = (Bd.ladderBase H).rowAt z t :=
    (rowAt_replicatedCompletion_castSucc hα hL hq _ _).trans
      ((Scheme.rowAt_mirror_castAdd _ _).trans
        (Scheme.rowAt_layerTowerEmb (B := Bd.towerBase H) (C := Bd.towerCat Γ A)
          (G := fun k ↦ Scheme.heightSet Γ B' k) z t m))
  -- the ladder
  let lad : Scheme.LadderPt Bd.S (Scheme.RankMember Bd.S H) H → Fin G.scheme.card :=
    fun p ↦ emb (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))
  let r : Scheme.RankMember Bd.S H → ℕ → Fin G.scheme.card := fun a i ↦
    lad (a, Sum.inl ⟨min i (H - 1), by omega⟩)
  have hlad (p q : Scheme.LadderPt Bd.S (Scheme.RankMember Bd.S H) H) :
      G.scheme.rowAt (lad p) (lad q) = ladderSource (Scheme.ladderCeil
        (Scheme.rankProf Bd.S H) p) (Scheme.baseIndex H
          (Scheme.rankProf Bd.S H) p.1 (Fin.natAdd _ (Scheme.ladderEquiv _ _ H q))) :=
    (hrowB _ _).trans (Scheme.rowAt_ladderBase_ladder Bd.wf p q)
  have hself (a : Scheme.RankMember Bd.S H) (i : ℕ) (hi : i < H) :
      Scheme.baseIndex H (Scheme.rankProf Bd.S H) a
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨min i (H - 1), by omega⟩))) =
        i + 1 := by
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H)
      ((a, Sum.inl ⟨min i (H - 1), by omega⟩) :
        Scheme.LadderPt Bd.S (Scheme.RankMember Bd.S H) H)
    simp only [Scheme.ladderCeil, Sum.elim_inl] at h
    rw [h]
    omega
  -- the context and donor cells are cells of the attachment
  have hctx (x : Fin I.left.card) : G.contextCell x = emb (Fin.castAdd _ (I.attachCtxCell g x)) :=
    cellMap_replicatedCompletion hα hL hq Fin.castSuccEmb Coatom.univ_map_left_ne
      mem_range_attachEmb_left
      (i := Fin.cast (congrArg Scheme.card (I.comap_left_attachment_scheme g)).symm x)
      (j := Fin.cast (congrArg Scheme.card G.comap_context).symm x) rfl
  have hdon (j : Fin d.card) : G.donorCell j = emb (Fin.castAdd _ (I.attachDonCell g hd j)) :=
    cellMap_replicatedCompletion hα hL hq _ (map_extendByLast_ne_univ g)
      mem_range_attachEmb_donor
      (i := Fin.cast (congrArg Scheme.card (I.comap_donor_attachment_scheme g hd)).symm j)
      (j := Fin.cast (congrArg Scheme.card G.comap_donor).symm j) rfl
  have hne (k : ℕ) : (Bd.towerCat Γ A (k + 2)).Nonempty :=
    ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun _ ↦ hΓ0,
      CellScheme.Rows.isLawful_const_bot, I.attachAdmits_bot g hd Q _⟩⟩
  -- a cell of full scope at the threshold
  obtain ⟨w, hw⟩ := Bd.exists_gradedIndex_univ_ladderTower (B' := B') hH hne m N (by omega)
    (by omega)
  refine ⟨G, ⟨(Fin.castAdd _ w).castSucc, (gradedIndex_replicatedCompletion_castSucc hα hL hq
      _).trans ((Scheme.gradedIndex_mirror_castAdd _).trans hw)⟩,
    Scheme.RankMember Bd.S H, H, r, hH, fun a i hi ↦ ?_, fun a i hi ↦ ?_,
    fun a i hi hi0 ↦ ?_, fun u hu ↦ ?_⟩
  · refine (hgi _).trans ?_
    change (Bd.S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  · refine (hlad _ _).trans ?_
    rw [hself a i hi]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    rw [show min i (H - 1) + 1 = i + 1 by omega]
  · refine (hlad _ _).trans ?_
    rw [hself a (i - 1) (by omega)]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    rw [show min i (H - 1) + 1 = i + 1 by omega, show i - 1 + 1 = i by omega]
  · -- the controllers: the cells of full scope below the apex are the cells of the tower
    obtain ⟨z, rfl⟩ : ∃ z : Fin (I.replicated g H Γ A B').card, u = Fin.castSucc z := by
      revert hu
      refine Fin.lastCases (n := (I.replicated g H Γ A B').card) (motive := fun u ↦
        G.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), N) →
          ∃ z : Fin (I.replicated g H Γ A B').card, u = Fin.castSucc z) ?_
          (fun z _ ↦ ⟨z, rfl⟩) u
      intro hu
      exfalso
      have h1 := congrArg Prod.snd
        (hu.symm.trans (gradedIndex_replicatedCompletion_last hα hL hq))
      simp only at h1
      omega
    have hz : (I.replicated g H Γ A B').toCellScheme.gradedIndex z =
        ((univ : Finset (Fin (m + 2))), N) :=
      (gradedIndex_replicatedCompletion_castSucc hα hL hq z).symm.trans hu
    obtain ⟨u', rfl⟩ : ∃ u' : Fin T.S.card, z = Fin.castAdd _ u' := by
      induction z using Fin.addCases with
      | left u' => exact ⟨u', rfl⟩
      | right j =>
        exfalso
        have h1 := (I.mem_mixedFaces g).mp (scope_replicated_natAdd j)
        exact h1.2.1 (congrArg Prod.fst hz)
    have hu' : T.S.toCellScheme.gradedIndex u' =
        ((univ : Finset (Fin (m + 2))), N - 2 + 2) := by
      rw [show N - 2 + 2 = N by omega]
      exact (Scheme.gradedIndex_mirror_castAdd u').symm.trans hz
    obtain ⟨R, hRC, hR, hrowA, hrowL⟩ :=
      Scheme.LadderBaseData.exists_controller_ladderTower (B := Bd) (A := A) (Γ := Γ)
        (B' := B') hcard (N - 2) m (by omega) u' hu'
    have hrowE (t : Fin (Bd.ladderBase H).card) :
        G.scheme.rowAt (Fin.castAdd _ u').castSucc (emb t) =
          T.S.rowAt u' (Bd.towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m t) :=
      (rowAt_replicatedCompletion_castSucc hα hL hq _ _).trans (Scheme.rowAt_mirror_castAdd _ _)
    have hread (c : Fin (I.attachment g).card) :
        G.scheme.rowAt (Fin.castAdd _ u').castSucc (emb (Fin.castAdd _ c)) =
          I.attachHatAt g N R c := by
      refine (hrowE _).trans ?_
      unfold attachHatAt
      split_ifs with hc
      · exact hrowA c (show (I.attachment g).toCellScheme.grade c ≤ N - 2 + 2 by omega)
      · apply Scheme.rowAt_of_notMem
        intro hmem
        have h1 : (T.S.toCellScheme.gradedIndex _).2 ≤ (T.S.toCellScheme.gradedIndex u').2 :=
          (show T.S.toCellScheme.gradedIndex _ ≤ T.S.toCellScheme.gradedIndex u' from hmem).2
        have hg : (T.S.toCellScheme.gradedIndex
            (Bd.towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m (Fin.castAdd _ c))).2 =
            (I.attachment g).toCellScheme.grade c :=
          congrArg Prod.snd (Bd.gradedIndex_baseCellEmb (H := H) (Γ := Γ) (A := A) (B' := B') m c)
        have h3 : (I.attachment g).toCellScheme.grade c ≤ N - 2 + 2 :=
          hg ▸ (h1.trans_eq (congrArg Prod.snd hu'))
        have h4 : (I.attachment g).toCellScheme.grade c ≤ N := by omega
        exact hc h4
    have hladu (p : Scheme.LadderPt Bd.S (Scheme.RankMember Bd.S H) H) :
        G.scheme.rowAt (Fin.castAdd _ u').castSucc (lad p) = posTable R (Scheme.baseIndex H
          (Scheme.rankProf Bd.S H) (Scheme.RankMember.ofLawful Bd.wf hcard hR)
            (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))) :=
      (hrowE _).trans (hrowL p)
    obtain ⟨-, htop, hval⟩ := Scheme.LadderBaseData.ladderController_clauses hH hcard hR
    have hrung (i : ℕ) (hi : i < H) :
        G.scheme.rowAt (Fin.castAdd _ u').castSucc
          (r (Scheme.RankMember.ofLawful Bd.wf hcard hR) i) = posTable R (i + 1) := by
      refine (hladu _).trans ?_
      rw [hself _ i hi]
    refine ⟨Scheme.RankMember.ofLawful Bd.wf hcard hR, posTable R, ?_, ?_,
      hrung, fun x hx hx0 ↦ ?_⟩
    · have hadm := (Scheme.LadderBaseData.mem_towerCat.mp hRC).2.2
        (show Q.threshold ≤ N - 2 + 2 by omega)
      have e1 : (fun x ↦ G.scheme.rowAt (Fin.castAdd _ u').castSucc (G.contextCell x)) =
          fun x ↦ I.attachHatAt g N R (I.attachCtxCell g x) :=
        funext fun x ↦ by rw [hctx]; exact hread _
      have e2 : (fun j ↦ G.scheme.rowAt (Fin.castAdd _ u').castSucc (G.donorCell j)) =
          fun j ↦ I.attachHatAt g N R (I.attachDonCell g hd j) :=
        funext fun j ↦ by rw [hdon]; exact hread _
      rw [e1, e2]
      exact hadm
    · rw [hctx, hread, hrung (H - 1) (by omega), show H - 1 + 1 = H by omega]
      unfold attachHatAt
      split_ifs
      · exact htop _
      · exact bot_le
    · rw [hctx, hread] at hx0 ⊢
      unfold attachHatAt at hx0 ⊢
      split_ifs at hx0 ⊢ with hc
      · exact hval _ hx0
      · exact absurd rfl hx0

end Seed

end VaughtConjecture

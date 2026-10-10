/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SeedLadderCompletion
import VaughtConjecture.MainTheorem.GrowthCarrierExistence
import VaughtConjecture.Continuation.GrowthLadderRecognition

/-!
# The ladder growth carrier at the seed position

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

**The old cells of a completion.**  In the completion of a completion below the full grade
(`CompletionBelowFullGrade.completion`: the scheme with the apex appended), the cells of the
scheme keep their rows and graded indices (`CompletionBelowFullGrade.rowAt_completion_castSucc`),
and along every proper face the cells of the completion are the old cells of the amalgam, in their
order (`CompletionBelowFullGrade.cellMap_completion`).

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

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- **The completion reads the old cells as the scheme does.** -/
theorem rowAt_completion_castSucc (z x : Fin F.scheme.card) :
    (F.completion hα).toScheme.rowAt z.castSucc x.castSucc = F.scheme.rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := F.isLegalBelowFullGrade.not_le) z x

/-- The old cells keep their graded indices in the completion. -/
theorem completion_gradedIndex_castSucc (z : Fin F.scheme.card) :
    (F.completion hα).toCellScheme.gradedIndex z.castSucc = F.scheme.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has the full grade. -/
theorem completion_gradedIndex_last :
    (F.completion hα).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- **Along a proper face the cells of the completion are the old cells of the amalgam**, in
their order. -/
theorem cellMap_completion {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    {i : Fin (I.amalgam.toScheme.comap f).card}
    {j : Fin ((F.completion hα).toScheme.comap f).card} (hij : (i : ℕ) = j) :
    (F.completion hα).toScheme.cellMap f j =
      (F.embed (I.amalgam.toScheme.cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range f (S := I.amalgam.toScheme)
    (T := (F.completion hα).toScheme) (φ := fun d ↦ (F.embed d).castSucc)
    (fun a b hab ↦ Fin.castSucc_lt_castSucc_iff.mpr (F.embed.strictMono hab)) (fun d ↦ ?_)
    (fun z hz ↦ ?_) hij
  · change (F.scheme.appendFullCellScheme (m + 2)).scope (F.embed d).castSucc = _
    rw [Scheme.appendFullCellScheme_scope_castSucc, F.scope_embed]
  · induction z using Fin.lastCases with
    | last =>
      exfalso
      change (((F.truncate hα).toScheme.appendFullCellScheme (m + 2)).scope (Fin.last _) :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_last, coe_univ] at hz
      exact hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ := hz (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
    | cast z =>
      change (((F.truncate hα).toScheme.appendFullCellScheme (m + 2)).scope z.castSucc :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
      have hz' : (F.scheme.toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f := hz
      obtain ⟨d, rfl⟩ := F.mem_range_embed z fun he ↦ hf (eq_univ_of_forall fun x ↦ by
        rw [he, coe_univ] at hz'
        obtain ⟨y, rfl⟩ := hz' (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
      exact ⟨d, rfl⟩

end CompletionBelowFullGrade

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) {e₀ : Fin n ↪ Fin m}
  {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- The face of the second coatom type along the root followed by the new point is the face of
the amalgam along the root followed by the new point. -/
theorem restrictFace_donor_amalgam (hd : restrictFace (extendByLast e₀) I.right = some d) :
    restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d := by
  have hright : restrictFace (Coatom.right m) I.amalgam = some I.right := I.restrictFace_right
  rw [← extendByLast_trans, ← restrictFace_trans I.amalgam _ _ hright]
  exact hd

/-- The context face of the amalgam is the first coatom type, as schemes. -/
theorem comap_left_amalgam_scheme :
    I.amalgam.toScheme.comap Fin.castSuccEmb = I.left.toScheme :=
  congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp I.restrictFace_left).2

include hd in
/-- The donor face of the amalgam is the donor, as schemes. -/
theorem comap_donor_amalgam_scheme :
    I.amalgam.toScheme.comap (extendByLast (e₀.trans Fin.castSuccEmb)) = d.toScheme :=
  congrArg StageType.toScheme
    ((restrictFace_eq_some_iff _ _).mp hd).2

/-- The cell of the amalgam at a cell of the context. -/
noncomputable def ctxCell (x : Fin I.left.card) : Fin I.amalgam.card :=
  I.amalgam.toScheme.faceCell Fin.castSuccEmb I.comap_left_amalgam_scheme x

/-- The cell of the amalgam at a cell of the donor. -/
noncomputable def donorFaceCell (j : Fin d.card) : Fin I.amalgam.card :=
  I.amalgam.toScheme.faceCell (extendByLast (e₀.trans Fin.castSuccEmb))
    (I.comap_donor_amalgam_scheme hd) j

/-- The **truncation at the grade `N`** of a state: its values at the cells of grade at most `N`,
`⊥` above. -/
def hatAt (N : ℕ) (R : Fin I.amalgam.card → Label.{u}) (c : Fin I.amalgam.card) : Label.{u} :=
  if I.amalgam.toCellScheme.grade c ≤ N then R c else ⊥

/-- The **admission predicate of the ladder tower** for requests `Q`: from the threshold on, the
truncation of the state at the threshold, read on the context and donor cells of the amalgam, is
admitted on the exact class. -/
def towerAdmits (Q : GrowthRequests I.left d.toScheme) (k : ℕ)
    (R : Fin I.amalgam.card → Label.{u}) : Prop :=
  Q.threshold ≤ k → Q.AdmitsOnClass (fun x ↦ I.hatAt Q.threshold R (I.ctxCell x))
    (fun j ↦ I.hatAt Q.threshold R (I.donorFaceCell hd j))

theorem towerAdmits_succ (Q : GrowthRequests I.left d.toScheme) (k : ℕ)
    (R : Fin I.amalgam.card → Label.{u}) (h : I.towerAdmits hd Q (k + 3) R) :
    I.towerAdmits hd Q (k + 2) R := fun hk ↦ h (by omega)

/-- The bottom state is admitted: its cap value is `⊥`. -/
theorem towerAdmits_bot (Q : GrowthRequests I.left d.toScheme) (k : ℕ) :
    I.towerAdmits hd Q k fun _ ↦ ⊥ := fun _ _ hcap ↦
  absurd (by simp only [hatAt, ite_self]) hcap

end Seed

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {e₀ : Fin n ↪ Fin m}
  {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **The ladder growth carrier at the seed position**, from the open bountifulness of the ladder
tower: at a stage that is zero or a limit, for requests `Q` on the donor with threshold at least
`2`, a height `H ≥ 1` at least the number of cells of the amalgam, values of the states in a finite
set `Γ` containing `⊥`, below the top of the grid at the grade `2` and below `ω ^ 2`, if the
ladder tower with the admission predicate of `Q` is bountiful and carries a lawful labelling
extending the glued labels, then its completion is a growth carrier with the context `I.left` and
the donor `d` as literal faces, a field ladder of height `H`, and every cell of full scope at the
threshold a ladder controller. -/
theorem exists_ladderCarrier (hα : Order.IsSuccPrelimit α) (Q : GrowthRequests I.left d.toScheme)
    (hN : 2 ≤ Q.threshold) {H : ℕ} (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    {Γ : Finset Label.{u}} (hΓ0 : ⊥ ∈ Γ) {B' : ℕ} (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hbount : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.IsBountiful)
    (hlab : ∃ q : Fin (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.card → Label.{u},
      (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.IsLawful q ∧
        ∀ c, q (I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' c) = I.amalgam.label c) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (e₀.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
        (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H, 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F := by
  classical
  set A := I.towerAdmits hd Q with hA
  have hne (k : ℕ) : (I.towerCat Γ A (k + 2)).Nonempty :=
    ⟨fun _ ↦ ⊥, mem_towerCat.mpr ⟨fun _ ↦ hΓ0, CellScheme.Rows.isLawful_const_bot,
      I.towerAdmits_bot hd Q _⟩⟩
  set F := ladderCompletion (A := A) hH hcard hΓ hΓω (I.towerAdmits_succ hd Q) hne hbount hlab
    with hF
  have hdonne : univ.map (extendByLast (e₀.trans Fin.castSuccEmb)) ≠
      (univ : Finset (Fin (m + 2))) := fun he ↦ by
    have h := mem_univ (Fin.castSucc (Fin.last m) : Fin (m + 2))
    rw [← he, mem_map] at h
    obtain ⟨a, -, ha⟩ := h
    induction a using Fin.lastCases with
    | last => rw [extendByLast_last] at ha; exact absurd ha (Fin.castSucc_lt_last _).ne'
    | cast a =>
      rw [extendByLast_castSucc, Function.Embedding.trans_apply] at ha
      have ha' := Fin.castSucc_injective _ ha
      simp at ha'
  have hdX : restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) (F.completion hα) =
      some d := by
    exact (StageType.restrictFace_addApex _ _ _ hdonne).trans
      ((F.restrictFace_withLabel _ _ (F.truncate_label_embed hα) _ hdonne).trans hd)
  let G := GrowthCarrier.ofExtension (F.isLegal_completion hα)
    (F.restrictFace_left_completion hα) hdX
  set T := I.ladderTower H Γ A B' m with hT
  set N := Q.threshold with hNdef
  have hNm : N ≤ m + 1 := by
    have h1 := I.left.isWellFormed.isWellFormed.grade_le_card Q.cap
    have h2 : #(I.left.toCellScheme.scope Q.cap) ≤ m + 1 :=
      (card_le_univ _).trans (by simp)
    exact h1.trans h2
  -- the cells of the base in the completion
  let emb : Fin (I.towerBase H).S.card → Fin G.scheme.card := fun t ↦
    (Scheme.layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m
      t).castSucc
  have hgi (t : Fin (I.towerBase H).S.card) :
      G.scheme.toCellScheme.gradedIndex (emb t) = (I.ladderBase H).toCellScheme.gradedIndex t := by
    exact (F.completion_gradedIndex_castSucc hα _).trans
      (Scheme.gradedIndex_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
        (G := fun k ↦ grid k B') t m)
  have hrowB (z t : Fin (I.towerBase H).S.card) :
      G.scheme.rowAt (emb z) (emb t) = (I.ladderBase H).rowAt z t := by
    exact (F.rowAt_completion_castSucc hα _ _).trans
      (Scheme.rowAt_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
        (G := fun k ↦ grid k B') z t m)
  -- the ladder
  let lad : Scheme.LadderPt I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H →
      Fin G.scheme.card := fun p ↦ emb (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))
  let r : Scheme.RankMember I.amalgam.toScheme H → ℕ → Fin G.scheme.card := fun a i ↦
    lad (a, Sum.inl ⟨min i (H - 1), by omega⟩)
  have hlad (p q : Scheme.LadderPt I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H) :
      G.scheme.rowAt (lad p) (lad q) = ladderSource (Scheme.ladderCeil
        (Scheme.rankProf I.amalgam.toScheme H) p) (Scheme.baseIndex H
          (Scheme.rankProf I.amalgam.toScheme H) p.1 (Fin.natAdd _ (Scheme.ladderEquiv _ _ H q))) :=
    (hrowB _ _).trans (Scheme.rowAt_ladderBase_ladder I.amalgam.isWellFormed p q)
  have hself (a : Scheme.RankMember I.amalgam.toScheme H) (i : ℕ) (hi : i < H) :
      Scheme.baseIndex H (Scheme.rankProf I.amalgam.toScheme H) a
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨min i (H - 1), by omega⟩))) =
        i + 1 := by
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H)
      ((a, Sum.inl ⟨min i (H - 1), by omega⟩) :
        Scheme.LadderPt I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H)
    simp only [Scheme.ladderCeil, Sum.elim_inl] at h
    rw [h]
    omega
  -- the context and donor cells are old cells of the amalgam
  have hctx (x : Fin I.left.card) : G.contextCell x = emb (Fin.castAdd _ (I.ctxCell x)) :=
    F.cellMap_completion hα Fin.castSuccEmb Coatom.univ_map_left_ne
      (i := Fin.cast (congrArg Scheme.card I.comap_left_amalgam_scheme).symm x)
      (j := Fin.cast (congrArg Scheme.card G.comap_context).symm x) rfl
  have hdon (j : Fin d.card) : G.donorCell j = emb (Fin.castAdd _ (I.donorFaceCell hd j)) :=
    F.cellMap_completion hα _ hdonne
      (i := Fin.cast (congrArg Scheme.card (I.comap_donor_amalgam_scheme hd)).symm j)
      (j := Fin.cast (congrArg Scheme.card G.comap_donor).symm j) rfl
  -- a cell of full scope at the threshold
  have hfullT : ∃ w, T.S.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), N) := by
    refine exists_gradedIndex_ladderTower hH hne ⟨?_, by omega, by simp; omega⟩ (by omega)
    rw [I.faces_ladderTower]
    exact I.amalgam.isWellFormed.univ_mem_faces
  obtain ⟨w, hw⟩ := hfullT
  refine ⟨G, ⟨w.castSucc, (F.completion_gradedIndex_castSucc hα w).trans hw⟩,
    Scheme.RankMember I.amalgam.toScheme H, H, r, hH, fun a i hi ↦ ?_, fun a i hi ↦ ?_,
    fun a i hi hi0 ↦ ?_, fun u hu ↦ ?_⟩
  · refine (hgi _).trans ?_
    change (I.amalgam.toScheme.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  · refine (hlad _ _).trans ?_
    rw [hself a i hi]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    rw [show min i (H - 1) + 1 = i + 1 by omega]
  · refine (hlad _ _).trans ?_
    rw [hself a (i - 1) (by omega)]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    rw [show min i (H - 1) + 1 = i + 1 by omega, show i - 1 + 1 = i by omega]
  · -- the controllers
    obtain ⟨u', rfl⟩ : ∃ u' : Fin T.S.card, u = Fin.castSucc u' := by
      revert hu
      refine Fin.lastCases (n := T.S.card) (motive := fun u ↦
        G.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), N) →
          ∃ u' : Fin T.S.card, u = Fin.castSucc u') ?_ (fun u' _ ↦ ⟨u', rfl⟩) u
      intro hu
      exfalso
      have h1 := congrArg Prod.snd (hu.symm.trans (F.completion_gradedIndex_last hα))
      simp only at h1
      omega
    have hu' : T.S.toCellScheme.gradedIndex u' =
        ((univ : Finset (Fin (m + 2))), N - 2 + 2) := by
      rw [show N - 2 + 2 = N by omega]
      exact (F.completion_gradedIndex_castSucc hα u').symm.trans hu
    obtain ⟨R, hRC, hR, hrowA, hrowL⟩ :=
      exists_controller_ladderTower (A := A) (Γ := Γ) (B' := B') hcard (N - 2) m (by omega) u' hu'
    have hread (c : Fin I.amalgam.card) :
        G.scheme.rowAt u'.castSucc (emb (Fin.castAdd _ c)) = I.hatAt N R c := by
      refine (F.rowAt_completion_castSucc hα u' _).trans ?_
      unfold hatAt
      split_ifs with hc
      · exact hrowA c (by omega)
      · apply Scheme.rowAt_of_notMem
        intro hmem
        have h1 : (T.S.toCellScheme.gradedIndex _).2 ≤ (T.S.toCellScheme.gradedIndex u').2 :=
          (show T.S.toCellScheme.gradedIndex _ ≤ T.S.toCellScheme.gradedIndex u' from hmem).2
        have hg : (T.S.toCellScheme.gradedIndex (Scheme.layerTowerEmb (B := I.towerBase H)
            (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m
              (Fin.castAdd _ c : Fin (I.towerBase H).S.card))).2 =
            I.amalgam.toCellScheme.grade c := by
          refine (congrArg Prod.snd (Scheme.gradedIndex_layerTowerEmb (B := I.towerBase H)
            (C := I.towerCat Γ A) (G := fun k ↦ grid k B') _ m)).trans ?_
          change (I.amalgam.toScheme.appendFullCellsScheme 1 _).grade (Fin.castAdd _ c) = _
          exact Scheme.appendFullCellsScheme_grade_castAdd _ _ _ c
        have h3 : I.amalgam.toCellScheme.grade c ≤ N - 2 + 2 :=
          hg ▸ (h1.trans_eq (congrArg Prod.snd hu'))
        exact hc (by omega)
    have hladu (p : Scheme.LadderPt I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H) :
        G.scheme.rowAt u'.castSucc (lad p) = posTable R (Scheme.baseIndex H
          (Scheme.rankProf I.amalgam.toScheme H)
            (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR)
            (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))) :=
      (F.rowAt_completion_castSucc hα u' _).trans (hrowL p)
    obtain ⟨-, htop, hval⟩ := ladderController_clauses hH hcard hR
    have hrung (i : ℕ) (hi : i < H) :
        G.scheme.rowAt u'.castSucc
          (r (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR) i) =
          posTable R (i + 1) := by
      refine (hladu _).trans ?_
      rw [hself _ i hi]
    refine ⟨Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR, posTable R, ?_, ?_,
      hrung, fun x hx hx0 ↦ ?_⟩
    · have hadm := (mem_towerCat.mp hRC).2.2 (show Q.threshold ≤ N - 2 + 2 by omega)
      have e1 : (fun x ↦ G.scheme.rowAt u'.castSucc (G.contextCell x)) =
          fun x ↦ I.hatAt N R (I.ctxCell x) := funext fun x ↦ by rw [hctx]; exact hread _
      have e2 : (fun j ↦ G.scheme.rowAt u'.castSucc (G.donorCell j)) =
          fun j ↦ I.hatAt N R (I.donorFaceCell hd j) := funext fun j ↦ by rw [hdon]; exact hread _
      rw [e1, e2]
      exact hadm
    · rw [hctx, hread, hrung (H - 1) (by omega), show H - 1 + 1 = H by omega]
      unfold hatAt
      split_ifs
      · exact htop _
      · exact bot_le
    · rw [hctx, hread] at hx0 ⊢
      unfold hatAt at hx0 ⊢
      split_ifs at hx0 ⊢ with hc
      · exact hval _ hx0
      · exact absurd rfl hx0

end Seed

end VaughtConjecture

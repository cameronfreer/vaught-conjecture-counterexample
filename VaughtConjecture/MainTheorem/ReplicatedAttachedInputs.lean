/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftAmbient
import VaughtConjecture.MainTheorem.ReplicatedLabel

/-!
# The lifts from the faces of the attachment into the mixed faces

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces of the replicated carrier).

The lifts into the mixed faces (`Seed.HasMixedLifts`) reduce to the same-grade lifts from a face
`V` inside the context face or the donor face into a mixed face `U ⊇ V`
(`Seed.HasAttachedMixedLifts`, `Seed.hasMixedLifts_of_attachedMixedLifts`).  Here these are
reduced further, through the full face (`Seed.cappedLift_attached_mixed_of_univ`): a lift from
`(V, k)` into `(univ, k)` gives the lift into `(U, k)`.

* **At the grade one**, at the seed position (`Seed.attachedMixedLift_one_of_restrictFace`): the
  donor face and the root are faces of the amalgam (`Seed.donor_mem_faces`,
  `Seed.root_mem_faces`) and the root has `n > 0` points (`Seed.card_root`).
* **Inside the context face** (`Seed.cappedLift_attached_univ_of_context`): the lift of the
  attachment from `(V, k)` into the context coatom, then the context lift (`Seed.HasContextLift`).
* **Inside the donor face** (`Seed.cappedLift_attached_univ_of_stateLift`): from the state lift
  from `V` (`Seed.AttachedStateLift`: a complete lawful state of the attachment satisfying
  `A (m + 2)`, the prescription on the cells below `(V, k)`, with the observation of the ambient)
  and the extension over the tower (`Seed.TowerExtension`), as for the context lift.  The state
  lift holds when the catalogue predicate holds for the states vanishing above `k`
  (`Seed.attachedStateLift_of_vanishing`, by `Seed.cappedLift_attachment_univ`): for the admission
  predicate, at every grade below the threshold (`Seed.attachAdmits_of_vanishing`).

**The state lift from the donor face at the threshold** (`Seed.attachedStateLift_donor`).  A face
inside the donor face has at most `n + 1` points and the threshold is at least `n + 1`
(`ClassCalibrated.arity`), so the only pair of a face inside the donor face at the threshold or
above is the donor face at the grade `n + 1`, when that is the threshold.  There the cells of the
top grade of the context are capped at the cap `c` (`CellScheme.Rows.isLawfulBelow_capOn`): the
cap value of the state is then at most `c`, and on the exact class it reads the requests as the
ambient's state does (admitted, `Seed.ambientAdmitted`) capped at `c`.

**The assembly** (`Seed.hasAttachedMixedLifts_attachAdmits`, `Seed.hasMixedLifts_attachAdmits`,
`Seed.replicatedInputs_of_towerExtension`): for requests calibrated on the class with the labels
pair admitted and the relative lift on the exact class, over a legal donor with a nonempty root,
the lifts into the mixed faces follow from the extension over the tower (`Seed.TowerExtension`) at
every grade alone; with a root that is not onto, so do all the inputs of the replicated scheme.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The lift from a face of the attachment into a mixed face at the grade one, at the seed
position**: from the donor as a face of the amalgam, the root as a face of the context, and a
nonempty root (`Seed.cappedLift_attached_mixed_one_of_faces`). -/
theorem attachedMixedLift_one_of_restrictFace (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hn : 0 < n)
    {V U : Finset (Fin (m + 2))} (hVF : V ∈ (I.replicated g H Γ A B').toCellScheme.faces)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hU : U ∈ I.mixedFaces g) (h : V ⊆ U) (hV1 : 1 ≤ #V) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (V, 1)) (Y := (U, 1)) ⟨h, le_rfl⟩ :=
  cappedLift_attached_mixed_one_of_faces hH hcard hΓ hA (donor_mem_faces hd) (root_mem_faces hte)
    (by rw [card_root]; omega) hU (faces_replicated ▸ hVF) hV1 h hV

/-- **Inside the context face, through the context lift**: for a face `V` inside the context face
and `1 ≤ k ≤ |V|`, the replicated scheme lifts capped from `(V, k)` into `(univ, k)` given the
context lift: within the context coatom it is the amalgam
(`Seed.cappedLift_replicated_of_subset`). -/
theorem cappedLift_attached_univ_of_context (hctx : I.HasContextLift g H Γ A B')
    {V : Finset (Fin (m + 2))} (hVF : V ∈ (I.replicated g H Γ A B').toCellScheme.faces)
    (hVC : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))) {k : ℕ} (hk1 : 1 ≤ k)
    (hkV : k ≤ #V) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (V, k))
      (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨subset_univ _, le_rfl⟩ := by
  have hCe : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) = ctxCoatom m :=
    map_castSuccEmb_eq_ctxCoatom
  have hCc : #(ctxCoatom m) = m + 1 := by
    rw [← hCe, card_map, card_univ, Fintype.card_fin]
  have hkm : k ≤ m + 1 := hkV.trans (hCc ▸ card_le_card (hCe ▸ hVC))
  have hCF : ctxCoatom m ∈ (I.replicated g H Γ A B').toCellScheme.faces := by
    rw [faces_replicated, ← hCe]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hsub := cappedLift_replicated_of_subset (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
    (B' := B') (X := (V, k)) (Y := (ctxCoatom m, k)) ⟨hVF, hk1, hkV⟩ ⟨hCF, hk1, hCc ▸ hkm⟩
    ⟨hCe ▸ hVC, le_rfl⟩ (.inl (hCe ▸ subset_rfl))
  exact hsub.trans (hctx k hk1 hkm)

variable (I g H Γ A B') in
/-- **The state lift from a face `V` at the grade `k`** over the replicated scheme: for a cap `c`
self-visible at `k`, a prescription `p` lawful below `(V, k)` and an ambient `q` lawful below
`(univ, k)` with the same observation at `c` below `(V, k)`, a complete lawful state of the
attachment satisfying `A (m + 2)`, equal to `p` at the cells below `(V, k)`, with the observation
of `q` at `c` at the cells of the attachment below `(univ, k)`. -/
def AttachedStateLift (V : Finset (Fin (m + 2))) (k : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible k c →
    ∀ (p : (I.replicated g H Γ A B').toCellScheme.below (V, k) → Label.{u})
      (q : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), k) → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow (V, k) p →
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) q →
      (∀ d, min (q (Set.inclusion (CellScheme.below_mono _
        (⟨subset_univ _, le_rfl⟩ : ((V, k) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, k))) d)) c =
        min (p d) c) →
      ∃ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P ∧
        A (m + 2) P ∧
        (∀ (d : (I.replicated g H Γ A B').toCellScheme.below (V, k)) a,
          I.attachEmb g H Γ A B' a = d.1 → P a = p d) ∧
        ∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), k)) a,
          I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c

/-- **Inside the context face or the donor face, through the state lift**: the state lift from `V`
and the extension over the tower give the capped lift from `(V, k)` into `(univ, k)` (as for the
context lift, `Seed.cappedLift_context_of_towerExtension`). -/
theorem cappedLift_attached_univ_of_stateLift {V : Finset (Fin (m + 2))}
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) {k : ℕ}
    (hS : AttachedStateLift I g H Γ A B' V k) (hE : TowerExtension I g H Γ A B' k) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (V, k))
      (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨subset_univ _, le_rfl⟩ := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨P, hPl, hPA, hPp, hPq⟩ := hS c hc p q hp hq hpq
  obtain ⟨q', hq', hq'P, hq'q⟩ := hE c hc q hq P hPl hPA hPq
  refine ⟨q', hq', hq'q, fun d ↦ ?_⟩
  obtain ⟨a, ha⟩ := mem_range_attachEmb (I := I) (g := g) (H := H) (Γ := Γ) (A := A) (B' := B')
    d.1 (hV.imp (fun h ↦ d.2.1.trans h) fun h ↦ d.2.1.trans h)
  exact (hq'P _ a ha).trans (hPp d a ha)

/-- **The state lift from the faces of the attachment below the predicate**: when `A (m + 2)`
holds for every lawful state vanishing above the grade `k`, the state lift from a face `V` inside
the context face or the donor face holds at `k ≤ |V|`, given the donor face and the root as faces
of the amalgam with a nonempty root.  The prescription and the ambient are read on the attachment;
the attachment lifts capped from `(V, k)` into `(univ, k)` (`Seed.cappedLift_attachment_univ`); the
lifted section, `⊥` above the grade, is a complete lawful state. -/
theorem attachedStateLift_of_vanishing
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    {V : Finset (Fin (m + 2))} (hVF : V ∈ I.amalgam.toCellScheme.faces) {k : ℕ} (hk1 : 1 ≤ k)
    (hkV : k ≤ #V)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hvan : ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
      (∀ a, k < (I.attachment g).toCellScheme.grade a → P a = ⊥) → A (m + 2) P) :
    AttachedStateLift I g H Γ A B' V k := by
  classical
  intro c hc p q hp hq hpq
  have hp' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hp
  rw [comap_rows_attachEmb] at hp'
  have hq' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hq
  rw [comap_rows_attachEmb] at hq'
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp
    (cappedLift_attachment_univ hdF hrF hr1 hVF hk1 hkV hV) c hc _ _ hp' hq' fun d ↦ hpq ⟨_, _⟩
  set P : Fin (I.attachment g).card → Label.{u} :=
    Rows.extendBot ((univ : Finset (Fin (m + 2))), k) r with hPdef
  have hPb : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
      fun a ↦ P a := Rows.isLawfulBelow_extendBot.mpr hr
  have hvanP (a : Fin (I.attachment g).card) (ha : k < (I.attachment g).toCellScheme.grade a) :
      P a = ⊥ := by
    rw [hPdef]
    unfold Rows.extendBot
    split_ifs with h
    · exact absurd h.2 (not_le.mpr ha)
    · rfl
  have hPl : (I.attachment g).rows.IsLawful P := by
    have h2 := Rows.isLawfulBelow_extendAbove (K := m + 2) hPb
    refine Rows.isLawful_of_isLawfulBelow attachment_mem_below_top
      ((Rows.isLawfulBelow_congr (w := fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k
        then P a else ⊥) fun a _ ↦ ?_).mp h2)
    by_cases h : (I.attachment g).toCellScheme.grade a ≤ k
    · exact ite_eq_left h
    · rw [ite_eq_right h, hvanP a (not_le.mp h)]
  refine ⟨P, hPl, hvan P hPl hvanP, fun d a ha ↦ ?_, fun d a ha ↦ ?_⟩
  · have haV : a ∈ (I.attachment g).toCellScheme.below (V, k) :=
      (attachEmb_mem_below_iff a _).mp (ha ▸ d.2)
    have e1 : P a = r ⟨a, (I.attachment g).toCellScheme.below_mono
        (⟨subset_univ _, le_rfl⟩ : ((V, k) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, k)) haV⟩ :=
      Rows.extendBot_of_mem r _
    rw [e1, hrp ⟨a, haV⟩]
    congr 1
    exact Subtype.ext ha
  · have hau : a ∈ (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), k) :=
      (attachEmb_mem_below_iff a _).mp (ha ▸ d.2)
    have e1 : P a = r ⟨a, hau⟩ := Rows.extendBot_of_mem r _
    rw [e1, hrc ⟨a, hau⟩]
    congr 2
    exact Subtype.ext ha

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **States vanishing below the threshold are admitted**: a state vanishing above a grade below
the threshold is `⊥` at the cap. -/
theorem attachAdmits_of_vanishing
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) {k : ℕ} (hk : k < Q.threshold)
    {P : Fin (I.attachment g).card → Label.{u}}
    (hP : ∀ a, k < (I.attachment g).toCellScheme.grade a → P a = ⊥) (K : ℕ) :
    I.attachAdmits g hd Q K P := fun _ _ hcap ↦ absurd (by
  have hg : (I.attachment g).toCellScheme.grade (I.attachCtxCell g Q.cap) = Q.threshold :=
    grade_attachCtxCell Q.cap
  simp only [attachHatAt]
  rw [hg, ite_eq_left le_rfl, hP _ (hg ▸ hk)]) hcap

/-- **The state lift from the donor face at the threshold** `n + 1`, for requests calibrated on the
class over a nonempty root.  The attachment lifts the prescription on the donor face into the full
face (`Seed.cappedLift_attachment_univ`); the cells of the top grade outside the donor face (in the
context) are capped at the cap `c` (`CellScheme.Rows.isLawfulBelow_capOn`), so the value at the
cap cell is at most `c`.  On the exact class with a cap value other than `⊥` the cap `c` is not
`⊥` and the ambient has the same class; the ambient's state is admitted (`Seed.ambientAdmitted`),
its reads capped at `c` are those of the state (`StageType.GrowthRequests.CorrectAt.map`), and
capping at `c`, at least the cap value of the state, changes no read
(`StageType.GrowthRequests.CorrectAt.of_min`). -/
theorem attachedStateLift_donor (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hN : Q.threshold = n + 1) :
    AttachedStateLift I g H Γ (I.attachAdmits g hd Q) B'
      (univ.map (extendByLast (g.trans Fin.castSuccEmb))) (n + 1) := by
  classical
  intro c hc p q hp hq hpq
  have hp' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hp
  erw [comap_rows_attachEmb] at hp'
  have hq' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hq
  erw [comap_rows_attachEmb] at hq'
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hDdef
  have hDc : #D = n + 1 := by rw [hDdef, card_map, card_univ, Fintype.card_fin]
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp
    (cappedLift_attachment_univ (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; omega) (donor_mem_faces hd) (by omega) hDc.ge (.inr subset_rfl))
    c hc _ _ hp' hq' fun d ↦ hpq ⟨_, _⟩
  set P' : Fin (I.attachment g).card → Label.{u} :=
    Rows.extendBot ((univ : Finset (Fin (m + 2))), n + 1) r with hP'def
  have hP'b : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), n + 1)
      fun a ↦ P' a := Rows.isLawfulBelow_extendBot.mpr hr
  have hgc (a : Fin (I.attachment g).card) :
      (I.attachment g).toCellScheme.grade a ≤ #((I.attachment g).toCellScheme.scope a) :=
    (I.isWellFormed_attachment g).isWellFormed.grade_le_card a
  -- the cells of the top grade outside the donor face
  set K : Fin (I.attachment g).card → Prop := fun a ↦
    (I.attachment g).toCellScheme.grade a = n + 1 ∧ ¬ (I.attachment g).toCellScheme.scope a ⊆ D
    with hKdef
  set P : Fin (I.attachment g).card → Label.{u} := fun a ↦ if K a then min (P' a) c else P' a
    with hPdef
  have hPb : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), n + 1)
      fun a ↦ P a := by
    refine Rows.isLawfulBelow_capOn hP'b hc K (fun a h ↦ h.1) (fun e s he hes hs ↦ ?_)
      (fun s t hst hg ht hKt ↦ ?_) (fun u t hu hKt ↦ ?_)
    · have h1 : (I.attachment g).toCellScheme.grade e ≤ (I.attachment g).toCellScheme.grade s :=
        hes.2
      have h2 : (I.attachment g).toCellScheme.grade s ≤ n + 1 := hs.2
      exact ⟨by omega, fun hsD ↦ he.2 (hes.1.trans hsD)⟩
    · refine ⟨hg.trans hKt.1, fun hsD ↦ ?_⟩
      have htC : (I.attachment g).toCellScheme.scope t ⊆
          univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) :=
        (I.scope_attachment g t).resolve_right hKt.2
      have hroot := card_le_card (subset_inter (hst.trans htC) hsD)
      rw [card_root] at hroot
      have := hgc s
      omega
    · have hg' : (I.attachment g).toCellScheme.grade u = (I.attachment g).toCellScheme.grade t :=
        congrArg Prod.snd hu
      have hs' : (I.attachment g).toCellScheme.scope u = (I.attachment g).toCellScheme.scope t :=
        congrArg Prod.fst hu
      exact ⟨hg'.trans hKt.1, hs' ▸ hKt.2⟩
  have hvanP' (a : Fin (I.attachment g).card) (ha : n + 1 < (I.attachment g).toCellScheme.grade a) :
      P' a = ⊥ := by
    rw [hP'def]
    unfold Rows.extendBot
    split_ifs with h
    · exact absurd h.2 (not_le.mpr ha)
    · rfl
  have hvanP (a : Fin (I.attachment g).card) (ha : n + 1 < (I.attachment g).toCellScheme.grade a) :
      P a = ⊥ := by
    rw [hPdef]
    simp only [hvanP' a ha, min_bot_left, ite_self]
  have hPl : (I.attachment g).rows.IsLawful P := by
    have h2 := Rows.isLawfulBelow_extendAbove (K := m + 2) hPb
    refine Rows.isLawful_of_isLawfulBelow attachment_mem_below_top
      ((Rows.isLawfulBelow_congr (w := fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ n + 1
        then P a else ⊥) fun a _ ↦ ?_).mp h2)
    by_cases h : (I.attachment g).toCellScheme.grade a ≤ n + 1
    · exact ite_eq_left h
    · rw [ite_eq_right h, hvanP a (not_le.mp h)]
  have hPc (a : Fin (I.attachment g).card) : min (P a) c = min (P' a) c := by
    by_cases h : K a
    · simp only [hPdef, h, ite_true, min_assoc, min_self]
    · simp only [hPdef, h, ite_false]
  -- the observation of the ambient
  have hobs (dd : (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), n + 1)) (a : Fin (I.attachment g).card)
      (ha : I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a = dd.1) :
      min (P a) c = min (q dd) c := by
    have hau : a ∈ (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), n + 1) :=
      (attachEmb_mem_below_iff a _).mp (ha ▸ dd.2)
    have e1 : P' a = r ⟨a, hau⟩ := Rows.extendBot_of_mem r _
    rw [hPc, e1, hrc ⟨a, hau⟩]
    congr 2
    exact Subtype.ext ha
  refine ⟨P, hPl, fun _ hcls hcap y ↦ ?_, fun dd a ha ↦ ?_, hobs⟩
  · -- the admission
    have hcN : IsSelfVisible Q.threshold c := by rw [hN]; exact hc
    -- every cell: the truncations at the threshold agree capped at `c`
    have hagr (a : Fin (I.attachment g).card) :
        min (I.attachHatAt g Q.threshold P a) c =
          min (ambientState H Γ (I.attachAdmits g hd Q) B' q a) c := by
      unfold attachHatAt
      by_cases h : (I.attachment g).toCellScheme.grade a ≤ n + 1
      · rw [hN, ite_eq_left h]
        erw [ambientState_of_le a h]
        exact hobs _ a rfl
      · rw [hN, ite_eq_right h]
        erw [ambientState_of_lt a (not_le.mp h)]
    -- the cap cell is capped
    have hcapg : (I.attachment g).toCellScheme.grade (I.attachCtxCell g Q.cap) = n + 1 :=
      (grade_attachCtxCell Q.cap).trans hN
    have hcapK : K (I.attachCtxCell g Q.cap) := by
      refine ⟨hcapg, fun hsub ↦ not_map_castSuccEmb_subset_donor (g := g) ?_⟩
      have hsc : (I.attachment g).toCellScheme.scope (I.attachCtxCell g Q.cap) =
          univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) := by
        rw [attachCtxCell, Scheme.scope_faceCell, hQ.scope_cap]
      exact hsc ▸ hsub
    have hhat : I.attachHatAt g Q.threshold P (I.attachCtxCell g Q.cap) =
        min (P' (I.attachCtxCell g Q.cap)) c := by
      unfold attachHatAt
      rw [hcapg, hN, ite_eq_left le_rfl, hPdef]
      exact ite_eq_left hcapK
    have hle : I.attachHatAt g Q.threshold P (I.attachCtxCell g Q.cap) ≤ c :=
      hhat ▸ min_le_right _ _
    have hc0 : c ≠ ⊥ := fun h0 ↦ hcap (by beta_reduce; rw [hhat, h0, min_bot_right])
    have hbot (a : Fin (I.attachment g).card) :
        I.attachHatAt g Q.threshold P a = ⊥ ↔
          ambientState H Γ (I.attachAdmits g hd Q) B' q a = ⊥ := by
      have h := hagr a
      constructor
      · intro h0
        rw [h0, min_bot_left] at h
        exact (min_eq_bot.mp h.symm).resolve_right hc0
      · intro h0
        rw [h0, min_bot_left] at h
        exact (min_eq_bot.mp h).resolve_right hc0
    have hamb := ambientAdmitted hH hcard hΓ0 hd hQ hn (n + 1) hN.le q hq
      (fun x hx ↦ (hbot _).symm.trans (hcls x hx)) (fun h0 ↦ hcap ((hbot _).mpr h0)) y
    have hmap := hamb.map (θ := fun x ↦ min x c) (fun _ _ h ↦ min_le_min_right c h)
      (min_bot_left c) (fun i hi x ↦ (visibilityReplace_min_of_isSelfVisible hi hcN x).symm)
      (fun hj ↦ (hQ.ref y hj).2.1) hQ.marker.2.1
    have hmap' : Q.CorrectAt (fun x ↦ min (I.attachHatAt g Q.threshold P (I.attachCtxCell g x)) c)
        y (min (I.attachHatAt g Q.threshold P (I.attachDonCell g hd y)) c) := by
      have e1 : (fun x ↦ min (I.attachHatAt g Q.threshold P (I.attachCtxCell g x)) c) =
          (fun x ↦ min x c) ∘
            fun x ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x) :=
        funext fun x ↦ hagr _
      rw [e1, hagr]
      exact hmap
    exact hmap'.of_min hle hcN (fun hj ↦ (hQ.ref y hj).2.1) hQ.marker.2.1
  · -- the prescription on the donor face
    have haV : a ∈ (I.attachment g).toCellScheme.below (D, n + 1) :=
      (attachEmb_mem_below_iff a _).mp (ha ▸ dd.2)
    have hKa : ¬ K a := fun h ↦ h.2 haV.1
    have e1 : P' a = r ⟨a, (I.attachment g).toCellScheme.below_mono
        (⟨subset_univ _, le_rfl⟩ : ((D, n + 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, n + 1))
        haV⟩ := Rows.extendBot_of_mem r _
    rw [hPdef]
    simp only [hKa, ite_false]
    rw [e1, hrp ⟨a, haV⟩]
    congr 1
    exact Subtype.ext ha

/-- **The lifts from the faces of the attachment into the mixed faces, from the extension over
the tower**, for requests calibrated on the class with the labels pair admitted and the relative
lift on the exact class, over a legal donor with a nonempty root: inside the context face through
the context lift (`Seed.hasContextLift_attachAdmits_tower`), inside the donor face through the
state lift, which holds below the threshold (`Seed.attachedStateLift_of_vanishing`) and, for the
donor face at the grade `n + 1` when that is the threshold, by capping
(`Seed.attachedStateLift_donor`). -/
theorem hasAttachedMixedLifts_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hE : ∀ j, 1 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasAttachedMixedLifts g H Γ (I.attachAdmits g hd Q) B' := by
  intro V U k hVF hV hU h hk1 hkV
  have hA := attachAdmits_succ (I := I) (g := g) (hd := hd) Q
  have hA0 := attachAdmits_bot (I := I) (g := g) (hd := hd) Q
  have hVu : #V ≤ m + 1 := by
    have hlt : V ⊂ univ := ssubset_univ_iff.mpr fun he ↦
      ((I.mem_mixedFaces g).mp hU).2.1 (univ_subset_iff.mp (he ▸ h))
    have := card_lt_card hlt
    simp only [card_univ, Fintype.card_fin] at this
    omega
  have hkU : k ≤ #U := hkV.trans (card_le_card h)
  refine cappedLift_attached_mixed_of_univ hH hcard hΓ0 hΓ hA hA0 hU h hk1 (hkV.trans hVu) hkU ?_
  by_cases hVC : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))
  · exact cappedLift_attached_univ_of_context
      (hasContextLift_attachAdmits_tower hH hcard hΓ0 hte hdp hdL hn hd hQ hpair hrel hE)
      hVF hVC hk1 hkV
  have hVD := hV.resolve_left hVC
  have hDc : #(univ.map (extendByLast (g.trans Fin.castSuccEmb))) = n + 1 := by
    rw [card_map, card_univ, Fintype.card_fin]
  have hkD : k ≤ n + 1 := hkV.trans (hDc ▸ card_le_card hVD)
  refine cappedLift_attached_univ_of_stateLift hV ?_ (hE k hk1 (hkV.trans hVu))
  rcases Nat.lt_or_ge k Q.threshold with hkN | hkN
  · exact attachedStateLift_of_vanishing (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; omega) (faces_replicated ▸ hVF) hk1 hkV hV
      fun P _ hP ↦ attachAdmits_of_vanishing hd Q hkN hP _
  · have hN := hQ.arity
    have hkn : k = n + 1 := by omega
    have hVe : V = univ.map (extendByLast (g.trans Fin.castSuccEmb)) :=
      eq_of_subset_of_card_le hVD (by omega)
    subst hVe hkn
    exact attachedStateLift_donor hH hcard hΓ0 hte hn hd hQ (by omega)

/-- **The lifts into the mixed faces from the extension over the tower**
(`Seed.hasAttachedMixedLifts_attachAdmits`, `Seed.hasMixedLifts_of_attachedMixedLifts`). -/
theorem hasMixedLifts_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hE : ∀ j, 1 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasMixedLifts g H Γ (I.attachAdmits g hd Q) B' :=
  hasMixedLifts_of_attachedMixedLifts hH hcard hΓ0 hΓ
    (attachAdmits_succ (I := I) (g := g) (hd := hd) Q)
    (attachAdmits_bot (I := I) (g := g) (hd := hd) Q)
    (hasAttachedMixedLifts_attachAdmits hH hcard hΓ0 hΓ hte hdp hdL hn hd hQ hpair hrel hE)

/-- **The inputs of the replicated scheme from the extension over the tower**: for requests
calibrated on the class with the labels pair admitted and the relative lift on the exact class,
over a legal donor with a nonempty root and a root that is not onto, with values containing `⊥`
and the compressed labelling, the extension over the tower at every grade gives the inputs: the
mixed lifts (`Seed.hasMixedLifts_attachAdmits`), the context lift
(`Seed.hasContextLift_attachAdmits_tower`), the mixed-coatom lift (`Seed.hasMixedCoatomLift`) and
the labelling (`Seed.replicatedInputs_of_lifts`). -/
theorem replicatedInputs_of_towerExtension (hH : 0 < H) (hcard : (I.attachment g).card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hsub : ∀ c, I.compressedLabel g c ∈ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hg : ¬ Function.Surjective g)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hE : ∀ j, 1 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.ReplicatedInputs g hd Q :=
  replicatedInputs_of_lifts hd hpair hQ hH hcard hΓ0 hΓ hΓω hsub
    (hasMixedLifts_attachAdmits hH hcard hΓ0 hΓ hte hdp hdL hn hd hQ hpair hrel hE)
    (hasContextLift_attachAdmits_tower hH hcard hΓ0 hte hdp hdL hn hd hQ hpair hrel hE)
    (hasMixedCoatomLift hH hcard hΓ0 hΓ (attachAdmits_succ (I := I) (g := g) (hd := hd) Q)
      (attachAdmits_bot (I := I) (g := g) (hd := hd) Q) hg)

end Seed

end VaughtConjecture

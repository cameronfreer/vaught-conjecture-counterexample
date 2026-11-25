/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.MirrorMixedLift
import VaughtConjecture.ProcessRank.SpanMirrorLift

/-!
# The seed lift as an instance of the lift over a pure attachment

Process rank `ω₁`, the finite span of mutual rigidity: the lift of a mirrored scheme over the
attachment of a seed (`Seed.cappedLift_mirror_mixed_face`) is the instance of the lift over a pure
attachment (`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`) at the attachment of the seed,
its two coatom faces (the context face and the face of the donor), its mixed faces, and the rank
members with their rank vectors (`Seed.cappedLift_mirror_mixed_face_of_attachment`, with the
statement of the seed theorem).  The seed theorem keeps its own statement and proof.
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

set_option quotPrecheck false in
/-- The mirrored scheme. -/
local notation "𝔼" => Scheme.mirror hmix

/-- **The seed lift from the lift over a pure attachment**: the statement of
`Seed.cappedLift_mirror_mixed_face`, proved by instantiating
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`. -/
theorem cappedLift_mirror_mixed_face_of_attachment (hH : 0 < H)
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
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ :=
  ProcessRank.MirrorAttachment.cappedLift_mirror_mixed (Att := (I.attachmentBase g).S)
    (FA := univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)))
    (FB := univ.map (extendByLast (g.trans Fin.castSuccEmb))) (MF := I.mixedFaces g)
    (Pf := Scheme.RankMember (I.attachmentBase g).S H) (prof := Scheme.rankProf _ H)
    (fun _ hU ↦ ⟨one_le_card_of_mem_mixedFaces hU, ((I.mem_mixedFaces g).mp hU).2.1⟩)
    (fun _ _ ↦ Scheme.rankProf_le _ H _ _) hH hcons hpos hatt hcells (I.scope_attachment g)
    map_castSuccEmb_ne_univ (map_extendByLast_ne_univ g)
    (fun _ hU ↦ ⟨((I.mem_mixedFaces g).mp hU).2.2.1, ((I.mem_mixedFaces g).mp hU).2.2.2⟩)
    hlad hrowLL hrowLA hone hread hagree htwin hU hUW τ hτo hτg hexist hj1 hjU

end Seed

end VaughtConjecture

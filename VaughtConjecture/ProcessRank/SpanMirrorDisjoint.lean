/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.PlanAttachment
import VaughtConjecture.ProcessRank.SpanMirrorLift

/-!
# The lift over the disjoint attachment of two two-point faces

Process rank `ω₁`, the finite span of mutual rigidity: the geometry of the test with `K = 2`.  On
`Fin 4` the two pure faces are `leftFace = {0, 1}` and `rightFace = {2, 3}`; they are disjoint and
cover the ground set.  Plans on the two faces amalgamate over the empty closed face to a plan on
`Fin 4` restricting to each (`ProcessRank.MirrorAttachment.exists_disjointPlan`, from
`Geometry.IsPlan.amalgamate`).  The mixed faces of a plan `R` (`mixedFacesOf R`) are its faces
inside neither pure face, other than the ground set.

**Proved here (the geometric premises).**  Every mixed face has a point and is proper
(`mixedFacesOf_spec`), lies inside neither pure face (`not_subset_of_mem_mixedFacesOf`), and the
pure faces are proper.  The mirror premise `hmix` (no mixed face inside the scope of a cell of
proper scope) follows from the attachment premises (`hmix_of_attachment`).

**The instance** (`ProcessRank.MirrorAttachment.cappedLift_mirror_disjoint`): the lift from a
mixed face into a larger face of the mirrored scheme, with the remaining premises explicit:
* the attachment: a scheme `Att` on `Fin 4` with every cell inside `leftFace` or `rightFace`
  (`hAtt`), embedded in `T` keeping graded indices (`hatt`), and every cell of `T` of proper scope
  a cell of the attachment (`hproperScope`);
* the scheme `T`: consistent rows (`hcons`), positive grades (`hpos`);
* the rank profiles: bounded by `H` (`hprofc`), `0 < H`;
* the ladder: the ladder points at `(univ, 1)` (`hlad`), their rows (`hrowLL`), the reading of the
  cells of grade one of the attachment through their shadows (`hrowLA`), every cell at `(univ, 1)`
  a ladder point (`hone`);
* the controllers: every cell of full scope of grade at least two reads the ladder and the
  attachment through one member (`hreadMember`), agrees at shadows (`hshadow`), and has twins
  (`htwinAbove`); and cells of full scope at every grade from two to `j` (`hexist`).
None of these is proved here: they are the content of the master levels.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace ProcessRank.MirrorAttachment

/-- The left pure face `{0, 1}` of `Fin 4`. -/
def leftFace : Finset (Fin 4) := {0, 1}

/-- The right pure face `{2, 3}` of `Fin 4`. -/
def rightFace : Finset (Fin 4) := {2, 3}

/-- The mixed faces of a family of faces of `Fin 4`: inside neither pure face, other than the
ground set. -/
def mixedFacesOf (R : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  R.filter fun U ↦ ¬ U ⊆ leftFace ∧ ¬ U ⊆ rightFace ∧ U ≠ univ

theorem mixedFacesOf_spec {R : Finset (Finset (Fin 4))} :
    ∀ U ∈ mixedFacesOf R, 1 ≤ #U ∧ U ≠ univ := fun _ hU ↦ by
  obtain ⟨-, hl, -, hne⟩ := mem_filter.mp hU
  refine ⟨card_pos.mpr (nonempty_iff_ne_empty.mpr fun h ↦ hl (h ▸ empty_subset _)), hne⟩

theorem not_subset_of_mem_mixedFacesOf {R : Finset (Finset (Fin 4))} :
    ∀ U ∈ mixedFacesOf R, ¬ U ⊆ leftFace ∧ ¬ U ⊆ rightFace := fun _ hU ↦
  ⟨(mem_filter.mp hU).2.1, (mem_filter.mp hU).2.2.1⟩

/-- **Plans on the two pure faces amalgamate** over the empty closed face to a plan on `Fin 4`
restricting to each (`Geometry.IsPlan.amalgamate`). -/
theorem exists_disjointPlan {P Q : Finset (Finset (Fin 4))} (hP : Geometry.IsPlan leftFace P)
    (hQ : Geometry.IsPlan rightFace Q) :
    ∃ R, Geometry.IsPlan univ R ∧ Geometry.restrict R leftFace = P ∧
      Geometry.restrict R rightFace = Q := by
  have hi : leftFace ∩ rightFace = ∅ := by decide
  have hu : leftFace ∪ rightFace = univ := by decide
  obtain ⟨R, hR, hRP, hRQ⟩ := hP.amalgamate hQ (hi ▸ hP.empty_mem) (hi ▸ hQ.empty_mem)
    (by
      rw [hi]
      ext C
      simp only [Geometry.mem_restrict, subset_empty]
      exact ⟨fun ⟨_, h⟩ ↦ ⟨h ▸ hQ.empty_mem, h⟩, fun ⟨_, h⟩ ↦ ⟨h ▸ hP.empty_mem, h⟩⟩)
  exact ⟨R, hu ▸ hR, hRP, hRQ⟩

/-- **The mirror premise from the attachment premises**: no mixed face lies inside the scope of a
cell of proper scope, which is the scope of a cell of the attachment, inside a pure face. -/
theorem hmix_of_attachment {Att : Scheme.{u} 4} {T : Scheme.{u} 4} {R : Finset (Finset (Fin 4))}
    {att : Fin Att.card → Fin T.card}
    (hatt : ∀ e, T.toCellScheme.gradedIndex (att e) = Att.toCellScheme.gradedIndex e)
    (hproperScope : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (hAtt : ∀ e, Att.toCellScheme.scope e ⊆ leftFace ∨ Att.toCellScheme.scope e ⊆ rightFace) :
    ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ mixedFacesOf R, ¬ U ⊆ T.toCellScheme.scope c := by
  intro c hc U hU hUc
  obtain ⟨e, rfl⟩ := hproperScope c hc
  rw [show T.toCellScheme.scope (att e) = Att.toCellScheme.scope e from
    congrArg Prod.fst (hatt e)] at hUc
  obtain ⟨hl, hr⟩ := not_subset_of_mem_mixedFacesOf U hU
  exact (hAtt e).elim (fun h ↦ hl (hUc.trans h)) fun h ↦ hr (hUc.trans h)

variable {H : ℕ} {Att : Scheme.{u} 4} {R : Finset (Finset (Fin 4))}
  {Pf : Type} [Finite Pf] [Nonempty Pf] {prof : Pf → Fin Att.card → ℕ} {T : Scheme.{u} 4}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ mixedFacesOf R,
    ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin 4)} {att : Fin Att.card → Fin T.card}
  {lad : Scheme.LadderPt Att Pf H → Fin T.card}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H prof Prod.fst (Scheme.ladderCeil prof)

set_option quotPrecheck false in
/-- The mirrored scheme. -/
local notation "𝔼" => Scheme.mirror hmix

/-- **The lift over the disjoint attachment** of `{0, 1}` and `{2, 3}` in `Fin 4`: the instance of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` with the geometric premises proved; the
remaining premises (attachment, ladder, controllers) are explicit. -/
theorem cappedLift_mirror_disjoint (hprofc : ∀ q d, prof q d ≤ H) (hH : 0 < H)
    (hcons : T.rows.IsConsistent) (hpos : ∀ d, 1 ≤ T.toCellScheme.grade d)
    (hatt : ∀ e, T.toCellScheme.gradedIndex (att e) = Att.toCellScheme.gradedIndex e)
    (hproperScope : ∀ x, T.toCellScheme.scope x ≠ univ → ∃ e, x = att e)
    (hAtt : ∀ e, Att.toCellScheme.scope e ⊆ leftFace ∨ Att.toCellScheme.scope e ⊆ rightFace)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin 4)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p) (idx p.1 v))
    (hrowLA : ∀ p e, Att.toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin 4)), 1) →
      ∃ p, x = lad p)
    (hreadMember : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) → 2 ≤ K →
      ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, Att.toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (prof b e))
    (hshadow : ∀ f u K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
      T.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), k) → 2 ≤ k → k ≤ K →
      ∀ e, Att.toCellScheme.grade e = k → ∃ v,
        T.rowAt u (lad v) = T.rowAt u (att e) ∧
        min (T.rowAt f (lad v)) (T.rowAt f u) = min (T.rowAt f (att e)) (T.rowAt f u))
    (htwinAbove : ∀ f K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
      2 ≤ k → k ≤ K → ∀ e, Att.toCellScheme.grade e = k →
      ∃ et, T.toCellScheme.gradedIndex et = ((univ : Finset (Fin 4)), k) ∧
        T.rowAt f (att e) ≤ T.rowAt f et)
    (hU : U ∈ (mixedFacesOf R)) {W : Finset (Fin 4)} (hUW : U ⊆ W)
    (τ : Fin T.card → Fin (𝔼).card) (hτo : ∀ v, T.mirrorOrig ((mixedFacesOf R)) (τ v) = v) {j : ℕ}
    (hτg : ∀ v k, T.toCellScheme.gradedIndex v = ((univ : Finset (Fin 4)), k) → k ≤ j →
      (𝔼).toCellScheme.gradedIndex (τ v) = (W, k))
    (hexist : ∀ k, 2 ≤ k → k ≤ j → ∃ f, T.toCellScheme.gradedIndex f =
      ((univ : Finset (Fin 4)), k))
    (hj1 : 1 ≤ j) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ :=
  cappedLift_mirror_mixed (FA := leftFace) (FB := rightFace) (MF := mixedFacesOf R)
    mixedFacesOf_spec hprofc hH hcons hpos hatt hproperScope hAtt (by decide) (by decide)
        not_subset_of_mem_mixedFacesOf hlad hrowLL hrowLA hone hreadMember hshadow htwinAbove hU
        hUW τ hτo hτg hexist hj1 hjU

end ProcessRank.MirrorAttachment

end VaughtConjecture

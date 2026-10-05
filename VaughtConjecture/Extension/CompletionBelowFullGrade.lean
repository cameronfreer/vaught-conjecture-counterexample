/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Extension.Seed

/-!
# The completion of a seed below the full grade, and the coatom extension

Roadmap, Layer 3 (the coatom extension construction: from the completion below the full grade to
the coatom extension property with apex), checkpoint 2.1; semantic contract, items 2–4.

**The completion below the full grade** (`CompletionBelowFullGrade I`) of a seed `I` is the
conclusion of the recursion on the grade (roadmap, checkpoint 2.6): a scheme on `m + 2` points
that extends the amalgam of `I` by cells of full scope only, with a lawful labelling extending the
glued one.  Each clause is a separate field:

* the old cells: an order embedding of the cells of the amalgam, a lower embedding that keeps
  scopes, rows, and labels literally, whose image contains every cell of scope other than the
  ground set (so the new cells have full scope), and the same faces;
* legality below the full grade (`Scheme.IsLegalBelowFullGrade`): well formed, coded, consistent,
  bountiful, every cell of grade below `m + 2`, and complete below the full grade;
* the labelling: lawful, and equal to the glued labelling on the old cells.

The labels are arbitrary labels, not necessarily at the stage `α`: the recursion completes a lawful
labelling whose values need not lie below the stage.

**Truncation to the stage** (`CompletionBelowFullGrade.truncate`).  At a stage `α` that is zero or
a limit, the truncation replaces every label by its reduction `Label.reduce α` to the stage, once,
at the end: the reduced labelling is lawful (`CellScheme.Rows.IsLawful.reduce`), and on the old
cells it is still the glued labelling, since the glued labels already lie at the stage
(`Label.AtStage.reduce_eq`).  This gives a stage type on `m + 2` points whose faces along
embeddings onto proper subsets are those of the amalgam
(`CompletionBelowFullGrade.restrictFace_withLabel`); along the first coatom (which is not the
whole ground set, `Coatom.univ_map_left_ne`) it is the first coatom type
(`CompletionBelowFullGrade.restrictFace_left_truncate`).

**The completion** (`CompletionBelowFullGrade.completion`) is the truncation with the apex added
(`StageType.addApex`): it is legal, has a cell of full scope and full grade `m + 2` carrying the
largest label, the formal top, and its faces along the two coatoms are literally the two coatom
types of `I`, labels included (`CompletionBelowFullGrade.exists_coatomExtension`).  The apex is
added after the truncation; its label `⊤` is fixed by stage reduction (`Label.reduce_top`), so
the apex and its maximality do not depend on that order.

The literal faces are proved by the uniqueness of the enumeration of visible cells
(`Scheme.cellMap_eq_of_strictMono`): the cells of the amalgam among those of the truncation, and
the cells of the truncation among those of the completion, form strictly monotone lower embeddings
keeping scopes, rows, and labels, and every cell visible in a coatom has scope other than the
ground set, so it is old (`StageType.restrictFace_eq_of_strictMono`).

The same argument applies to any lawful labelling at the stage that extends the glued one
(`CompletionBelowFullGrade.exists_coatomExtension_of_label`).  When the labels of the completion
below the full grade already lie at the stage, no truncation and no hypothesis on the stage is
needed (`CompletionBelowFullGrade.exists_coatomExtension_of_atStage`).

**The coatom extension property** (`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`):
at a stage that is zero or a limit, if the seed of any two legal coatom types with a common face
(`Seed.ofCoatoms`) has a completion below the full grade, then
`StageType.HasApexCoatomExtensions α` holds, and hence `StageType.HasCoatomExtensions α`
(`StageType.HasCoatomExtensions.of_completionBelowFullGrade`).  The hypothesis, a completion below
the full grade of every such seed, has the same form at every arity: two coatom types on one point
over the empty face (`m = 0`) and on two points (`m = 1`) give seeds of the same shape.

## References

The coatom extension with apex is [Kni26, Corollary 4.3.22], whose proof reduces the completed
labelling to the stage.  The completion has the shape of [Kni26, Definition 4.3.14] (the old cells
kept, the new cells of full scope); its rows are not those of that definition.  For the completion,
consistency is the statement of [Kni26, Lemma 4.3.16] and bountifulness the statement of
[Kni26, Lemma 4.3.20]; neither printed proof is used.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-- The **completion below the full grade** of a seed `I`: a scheme on `m + 2` points extending the
amalgam of `I` by cells of full scope only, legal below the full grade, with a lawful labelling
extending the glued labelling of the amalgam.  Its labels need not lie at the stage.  It has the
shape of the completion of [Kni26, Definition 4.3.14] below the full grade (the old cells kept,
the new cells of full scope), not necessarily its rows. -/
structure CompletionBelowFullGrade {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) where
  /-- The completed scheme: cells, scopes, grades, faces, and rows, on `m + 2` points. -/
  scheme : Scheme.{u} (m + 2)
  /-- The old cells: the cells of the amalgam, in their order. -/
  embed : Fin I.amalgam.card ↪o Fin scheme.card
  /-- The old cells form a lower embedding of the amalgam: grades and the graded order are kept,
  and every cell below an old cell is old. -/
  isLowerEmbedding : I.amalgam.toCellScheme.IsLowerEmbedding scheme.toCellScheme embed
  /-- The old cells keep their scopes. -/
  scope_embed (d : Fin I.amalgam.card) : scheme.toCellScheme.scope (embed d) =
    I.amalgam.toCellScheme.scope d
  /-- The old cells keep their rows: the rows pull back to those of the amalgam. -/
  comap_rows : scheme.rows.comap isLowerEmbedding = I.amalgam.rows
  /-- Every cell of scope other than the ground set is old; the new cells have full scope. -/
  mem_range_embed (z : Fin scheme.card) :
    scheme.toCellScheme.scope z ≠ univ → z ∈ Set.range embed
  /-- The faces are those of the amalgam. -/
  faces_eq : scheme.toCellScheme.faces = I.amalgam.toCellScheme.faces
  /-- The scheme is legal below the full grade `m + 2`.  For the completion, consistency is the
  statement of [Kni26, Lemma 4.3.16] and bountifulness that of [Kni26, Lemma 4.3.20]. -/
  isLegalBelowFullGrade : scheme.IsLegalBelowFullGrade
  /-- The labelling of the cells, not necessarily at the stage. -/
  label : Fin scheme.card → Label.{u}
  /-- The labelling is a lawful section of the rows. -/
  isLawful : scheme.rows.IsLawful label
  /-- The old cells keep the glued labels of the amalgam. -/
  label_embed (d : Fin I.amalgam.card) : label (embed d) = I.amalgam.label d

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {q : Fin F.scheme.card → Label.{u}}

/-! ### Stage types on the completed scheme -/

/-- The completed scheme with a lawful labelling `q` at the stage `α`, as a stage type on `m + 2`
points. -/
def withLabel (hq : F.scheme.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d)) :
    StageType.{u} α (m + 2) where
  toScheme := F.scheme
  label := q
  isWellFormed := F.isLegalBelowFullGrade.isWellFormed
  isCoded := F.isLegalBelowFullGrade.isCoded
  isLawful := hq
  atStage := hqα

/-- **The faces along a proper face are those of the amalgam**, including definedness, for any
labelling at the stage extending the glued one. -/
theorem restrictFace_withLabel (hq : F.scheme.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d))
    (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ) :
    StageType.restrictFace f (F.withLabel hq hqα) = StageType.restrictFace f I.amalgam := by
  refine StageType.restrictFace_eq_of_strictMono (t := F.withLabel hq hqα) (s := I.amalgam) f
    (φ := F.embed) F.embed.strictMono F.isLowerEmbedding F.scope_embed F.comap_rows
    (F.isLegalBelowFullGrade.isWellFormed.ground_eq.trans I.amalgam.isWellFormed.ground_eq.symm)
    F.faces_eq hqe fun z hz ↦ F.mem_range_embed z fun he ↦ hf (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
  exact mem_map_of_mem _ (mem_univ y)

/-- The second coatom is not the whole ground set. -/
private theorem univ_map_right_ne : univ.map (Coatom.right m) ≠ univ := fun he ↦ by
  have h := mem_univ (Fin.castSucc (Fin.last m))
  rw [← he, Coatom.univ_map_right] at h
  exact notMem_erase _ _ h

/-- **The coatom extension with apex from a labelling at the stage** [Kni26, Corollary 4.3.22]:
for any lawful labelling of the completed scheme at the stage extending the glued one, adding the
apex gives a legal stage type on `m + 2` points whose faces along the two coatoms are the coatom
types of `I`, with a cell of full scope and full grade carrying the largest label. -/
theorem exists_coatomExtension_of_label (hq : F.scheme.rows.IsLawful q)
    (hqα : ∀ d, AtStage α (q d)) (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some I.left ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some I.right ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d :=
  ⟨(F.withLabel hq hqα).addApex F.isLegalBelowFullGrade (Nat.succ_pos _),
    StageType.isLegal_addApex _ _,
    (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
      ((F.restrictFace_withLabel hq hqα hqe _ Coatom.univ_map_left_ne).trans I.restrictFace_left),
    (StageType.restrictFace_addApex _ _ _ univ_map_right_ne).trans
      ((F.restrictFace_withLabel hq hqα hqe _ univ_map_right_ne).trans I.restrictFace_right),
    StageType.exists_apex_addApex _ _⟩

/-- **The coatom extension with apex when the labels already lie at the stage**: no truncation and
no hypothesis on the stage is needed. -/
theorem exists_coatomExtension_of_atStage (hF : ∀ d, AtStage α (F.label d)) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some I.left ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some I.right ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d :=
  F.exists_coatomExtension_of_label F.isLawful hF F.label_embed

/-! ### Truncation to the stage, and the completion -/

variable (hα : Order.IsSuccPrelimit α)

/-- The **truncation to the stage** `α`, zero or a limit: the completed scheme with its labels
reduced to the stage, once, by `Label.reduce α`; lawful by `CellScheme.Rows.IsLawful.reduce`. -/
noncomputable def truncate : StageType.{u} α (m + 2) :=
  F.withLabel (F.isLawful.reduce hα) fun _ ↦ atStage_reduce α _

/-- **The truncation keeps the glued labels on the old cells**: they already lie at the stage. -/
theorem truncate_label_embed (d : Fin I.amalgam.card) :
    (F.truncate hα).label (F.embed d) = I.amalgam.label d :=
  (congrArg (Label.reduce α) (F.label_embed d)).trans (I.amalgam.atStage d).reduce_eq

/-- **The face of the truncation along `Fin.castSuccEmb` is the first coatom type**, literally,
labels included. -/
theorem restrictFace_left_truncate :
    StageType.restrictFace (Coatom.left m) (F.truncate hα) = some I.left :=
  (F.restrictFace_withLabel _ _ (F.truncate_label_embed hα) _ Coatom.univ_map_left_ne).trans
    I.restrictFace_left

/-- The **completion** of a seed at a stage that is zero or a limit: the truncation with the apex
added: one cell of full scope and full grade `m + 2` labelled with the formal top. -/
noncomputable def completion : StageType.{u} α (m + 2) :=
  (F.truncate hα).addApex F.isLegalBelowFullGrade (Nat.succ_pos _)

/-- **The completion is legal.** -/
theorem isLegal_completion : (F.completion hα).IsLegal :=
  StageType.isLegal_addApex _ _

/-- **The completion has an apex**: a cell of full scope and full grade `m + 2` carrying the
largest label. -/
theorem exists_apex_completion :
    ∃ d, (F.completion hα).toCellScheme.gradedIndex d = (univ, m + 2) ∧
    ∀ e, (F.completion hα).label e ≤ (F.completion hα).label d :=
  StageType.exists_apex_addApex _ _

/-- **The face of the completion along `Fin.castSuccEmb` is the first coatom type**, literally,
labels included: the truncation keeps the glued labels. -/
theorem restrictFace_left_completion :
    StageType.restrictFace (Coatom.left m) (F.completion hα) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
    ((F.restrictFace_withLabel _ _ (F.truncate_label_embed hα) _ Coatom.univ_map_left_ne).trans
      I.restrictFace_left)

/-- **The face of the completion along `extendByLast Fin.castSuccEmb` is the second coatom
type**, literally, labels included: the truncation keeps the glued labels. -/
theorem restrictFace_right_completion :
    StageType.restrictFace (Coatom.right m) (F.completion hα) = some I.right :=
  (StageType.restrictFace_addApex _ _ _ univ_map_right_ne).trans
    ((F.restrictFace_withLabel _ _ (F.truncate_label_embed hα) _ univ_map_right_ne).trans
      I.restrictFace_right)

include F hα in
/-- **The coatom extension with apex from a completion below the full grade**
[Kni26, Corollary 4.3.22]: at a stage that is zero or a limit, a legal stage type on `m + 2` points
whose faces along the two coatoms are the coatom types of `I`, with a cell of full scope and full
grade carrying the largest label. -/
theorem exists_coatomExtension : ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧
    StageType.restrictFace Fin.castSuccEmb t = some I.left ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some I.right ∧
    ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d :=
  ⟨F.completion hα, F.isLegal_completion hα, F.restrictFace_left_completion hα,
    F.restrictFace_right_completion hα, F.exists_apex_completion hα⟩

end CompletionBelowFullGrade

namespace StageType

variable {α : Ordinal.{u}}

/-- **The coatom extension property with apex from completions below the full grade**
[Kni26, Corollary 4.3.22]: at a stage `α` that is zero or a limit, if the seed of any two legal
coatom types with the same face along `Fin.castSuccEmb` has a completion below the full grade, then
any two such types are the faces of one legal stage type with an apex. -/
theorem HasApexCoatomExtensions.of_completionBelowFullGrade (hα : Order.IsSuccPrelimit α)
    (hF : ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
      (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
      (hpb : restrictFace Fin.castSuccEmb tb = some p),
      Nonempty (CompletionBelowFullGrade (Seed.ofCoatoms hla hlb hpa hpb))) :
    HasApexCoatomExtensions.{u} α := fun m ta tb p hla hlb hpa hpb ↦
  (hF m ta tb p hla hlb hpa hpb).some.exists_coatomExtension hα

/-- **The coatom extension property from completions below the full grade**: forget the apex. -/
theorem HasCoatomExtensions.of_completionBelowFullGrade (hα : Order.IsSuccPrelimit α)
    (hF : ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
      (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
      (hpb : restrictFace Fin.castSuccEmb tb = some p),
      Nonempty (CompletionBelowFullGrade (Seed.ofCoatoms hla hlb hpa hpb))) :
    HasCoatomExtensions.{u} α :=
  (HasApexCoatomExtensions.of_completionBelowFullGrade hα hF).hasCoatomExtensions

/-- **The coatom extension property with apex from completions at the stage**: if the seed of any
two legal coatom types with the same face has a completion below the full grade whose labels lie
at the stage, then no hypothesis on the stage is needed. -/
theorem HasApexCoatomExtensions.of_completionBelowFullGrade_of_atStage
    (hF : ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
      (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
      (hpb : restrictFace Fin.castSuccEmb tb = some p),
      ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hla hlb hpa hpb),
        ∀ d, AtStage α (F.label d)) :
    HasApexCoatomExtensions.{u} α := fun m ta tb p hla hlb hpa hpb ↦
  let ⟨F, hF⟩ := hF m ta tb p hla hlb hpa hpb
  F.exists_coatomExtension_of_atStage hF

end StageType

end VaughtConjecture

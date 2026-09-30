/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Stage.Legal

/-!
# Pinned extensions from coatom extensions

Roadmap, Layer 3 (the exact pinned extension, row 6 of the table of 3.4, by one coatom extension
for each point of the chart outside the face; its base cases, the empty chart and the empty face);
semantic contract, item 4 (face maps are exact, and the absence of a face is information).

A **one-point pinned extension** of a legal stage type `P` on `n` points is a legal stage type `Q`
on `n + 1` points whose face along `Fin.castSuccEmb` is literally `P`, labels included.  For a
face `f : Fin m ↪ Fin n` of `P` and a one-point coface `d` of the restriction `p` of `P` along `f`
(a legal stage type on `m + 1` points whose face along `Fin.castSuccEmb` is `p`), it is **exact
over `f`** when its face along `extendByLast f`, the face `f` followed by the new point, is
literally `d`.

This file reduces the exact pinned extension to the coatom extension construction.

* `StageType.HasApexCoatomExtensions α` is [Kni26, Corollary 4.3.22] at stage `α`, in the
  arrangement used here: any two legal stage types on `m + 1` points, placed on the coatoms of
  `Fin (m + 2)` omitting the last point (`Fin.castSuccEmb`) and the point `m`
  (`extendByLast Fin.castSuccEmb`), which have the same face on the common `m` points, are the
  literal faces of one legal stage type on `m + 2` points having a cell of full scope and full
  grade that carries the largest label (the apex).  `StageType.HasCoatomExtensions α` is the same
  statement without the apex, and follows from it
  (`StageType.HasApexCoatomExtensions.hasCoatomExtensions`).  Both are existence statements, and
  hypotheses here, not theorems: the amalgam of the two stage types, with its two literal faces
  and its consistent and bountiful rows, is constructed in
  `VaughtConjecture.Extension.CoatomAmalgam` ([Kni26, Definition 4.3.1 and Lemma 4.3.2]); it has
  no cell of full scope, and its completion by such cells ([Kni26, Definition 4.3.14]), with the
  bountifulness of the completed rows ([Kni26, Lemma 4.3.20]), is not constructed.
* **The exact pinned extension** (`StageType.exists_pinned_extension`, row 6): under the weaker
  hypothesis, for every legal `P` at stage `α`, every closed face `f` of `P` with restriction `p`,
  and every legal one-point coface `d` of `p`, there is a legal one-point pinned extension of `P`
  exact over `f`.  It is built by one coatom extension for each point of `P` outside the face:
  a point `x` with the face extended by `x` closed (accessibility of the plan) is added to the
  face, the coatom extension amalgamates the restriction of `P` to the enlarged face with `d`,
  and the result is a one-point coface of the enlarged face.  Nothing about the stage `α` is used.
* **The face of the whole chart** (`StageType.exists_pinned_extension_of_surjective`): when `f`
  is onto, no coatom extension is needed; `d` itself, reindexed, is the extension.  The **empty
  chart** is this case (`StageType.exists_pinned_extension_of_isEmpty`).  The **empty face** is an
  instance of the general statement with `m = 0`.
* **The face must be closed**
  (`StageType.univ_map_mem_faces_of_isSome_restrictFace_extendByLast`): if some stage type
  restricts to `P` along `Fin.castSuccEmb` and has a face along `extendByLast f`, then `f` spans a
  closed face of `P`.
* Every legal scheme carries a legal stage type at every stage, its bottom labelling
  (`Scheme.IsLegal.toStageType`, [Kni26, Proposition 4.3.24] for the domains that are legal
  schemes); in particular the one-point scheme with mute rows (`Scheme.onePoint`) is legal
  (`Scheme.isLegal_onePoint`) and gives a legal one-point stage type at every stage.
* The amalgamation corollaries: under the same hypothesis every legal stage type has a legal
  one-point extension (`StageType.exists_extension`, [Kni26, Proposition 4.3.23]), and two legal
  stage types with a common face are faces of one legal stage type (`StageType.exists_amalgam`).

## Placement

`StageType.card_eq_zero`, `StageType.faces_eq_of_zero`, `StageType.eq_of_zero`, and
`StageType.isSome_restrictFace_of_zero` belong in `VaughtConjecture.Stage.Basic`;
`Scheme.IsLegal.toStageType` with `Scheme.IsLegal.isLegal_toStageType` in
`VaughtConjecture.Stage.Legal`; and `Scheme.onePoint` with `Scheme.isLegal_onePoint` in
`VaughtConjecture.Stage.LegalExamples`, where they would replace the private `point`.  They are
stated here so that those files are unchanged.

## References

The coatom extension is [Kni26, Corollary 4.3.22], built on the amalgam of
[Kni26, Definition 4.3.1] and its completion of [Kni26, Definition 4.3.14]; the one-point
extension and the existence of types on every domain are [Kni26, Propositions 4.3.23 and 4.3.24];
the one-point scheme with mute rows is the last clause of [Kni26, Lemma 4.2.2].
-/

universe u

namespace VaughtConjecture

open Finset

/-! ### Stage types on every legal scheme -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- The stage type at stage `α` on a legal scheme with every label bottom. -/
def IsLegal.toStageType (hS : S.IsLegal) (α : Ordinal.{u}) : StageType.{u} α n where
  toScheme := S
  label _ := ⊥
  isWellFormed := hS.isWellFormed
  isCoded := hS.isCoded
  isLawful := CellScheme.Rows.isLawful_bot
  atStage _ := Label.atStage_bot

/-- **Every legal scheme carries a legal stage type** [Kni26, Proposition 4.3.24]: its bottom
labelling. -/
theorem IsLegal.isLegal_toStageType (hS : S.IsLegal) (α : Ordinal.{u}) :
    (hS.toStageType α).IsLegal :=
  hS

/-- The **one-point scheme**: a single cell of scope `{0}` and grade `1`, the faces `∅` and `{0}`
(the interval plan on `Fin 1`), and mute rows. -/
def onePoint : Scheme.{u} 1 where
  card := 1
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := CellScheme.Rows.mute _

/-- **The one-point scheme is legal**: mute rows are consistent and bountiful, and the only graded
face is `({0}, 1)`, the graded index of its cell. -/
theorem isLegal_onePoint : onePoint.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [onePoint, CellScheme.gradedIndex]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isConsistent := CellScheme.Rows.isConsistent_mute
  isBountiful := CellScheme.Rows.isBountiful_mute
  isComplete := fun ⟨C, j⟩ ⟨_, hpos, hle⟩ ↦ ⟨(0 : Fin 1), by
    have hC : #C ≤ 1 := card_le_univ C
    have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp only at hpos hle ⊢; simp; omega)
    simp only at hpos hle
    ext <;> simp [CellScheme.gradedIndex, onePoint, hC']
    omega⟩

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### The coatom extension property -/

variable (α) in
/-- The **coatom extension property** at stage `α`: [Kni26, Corollary 4.3.22] without the maximal
full cell, in the arrangement used for pinned extensions.  Any two legal stage types `ta` and `tb`
on `m + 1` points with the same face along `Fin.castSuccEmb`, a closed face, are the faces of one
legal stage type on `m + 2` points along the coatom omitting the last point (`Fin.castSuccEmb`)
and the coatom omitting the point `m` (`extendByLast Fin.castSuccEmb`).

This is an existence statement, a hypothesis and not a theorem, while the completion of the amalgam
of `VaughtConjecture.Extension.CoatomAmalgam` is not constructed.  `exists_pinned_extension` uses
nothing about the stage `α`: the limit stage of row 6 enters only when this hypothesis is
discharged, through the stronger `HasApexCoatomExtensions`. -/
def HasCoatomExtensions : Prop :=
  ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m), ta.IsLegal → tb.IsLegal →
    restrictFace Fin.castSuccEmb ta = some p → restrictFace Fin.castSuccEmb tb = some p →
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb

variable (α) in
/-- The **coatom extension property with apex** at stage `α`: [Kni26, Corollary 4.3.22] in full,
in the arrangement used for pinned extensions.  Any two legal stage types `ta` and `tb` on `m + 1`
points with the same face along `Fin.castSuccEmb` are the faces, along `Fin.castSuccEmb` and
`extendByLast Fin.castSuccEmb`, of one legal stage type `t` on `m + 2` points which moreover has a
cell `Ξ` of full scope and full grade `m + 2` carrying the largest label of `t`,
`q(Ξ) = max ran q`.

This is an existence statement, a hypothesis and not a theorem, while the completion of the amalgam
of `VaughtConjecture.Extension.CoatomAmalgam` is not constructed; it is the form in which the
completion is to be proved, and the apex is what high-arity dominance [Kni26, Lemma 4.4.3] uses. -/
def HasApexCoatomExtensions : Prop :=
  ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m), ta.IsLegal → tb.IsLegal →
    restrictFace Fin.castSuccEmb ta = some p → restrictFace Fin.castSuccEmb tb = some p →
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d

/-- The coatom extension property with apex implies the coatom extension property: forget the
apex. -/
theorem HasApexCoatomExtensions.hasCoatomExtensions (hext : HasApexCoatomExtensions.{u} α) :
    HasCoatomExtensions.{u} α := fun m ta tb p hta htb hpa hpb ↦
  let ⟨t, ht, hta', htb', _⟩ := hext m ta tb p hta htb hpa hpb
  ⟨t, ht, hta', htb'⟩

/-! ### The face of the whole chart -/

/-- **The face of the whole chart.**  If the face `f` is onto, the coface `d`, reindexed, is a
one-point pinned extension of `P` exact over `f`. -/
theorem exists_pinned_extension_of_surjective {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} (hf : Function.Surjective f)
    (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d := by
  -- The face and its extension are bijections.
  have hbij : Function.Bijective f := ⟨f.injective, hf⟩
  have hbij' : Function.Bijective (extendByLast f) := by
    refine ⟨(extendByLast f).injective, fun y ↦ ?_⟩
    induction y using Fin.lastCases with
    | last => exact ⟨Fin.last m, by simp⟩
    | cast y =>
      obtain ⟨i, rfl⟩ := hf y
      exact ⟨i.castSucc, by simp⟩
  set F := Equiv.ofBijective f hbij
  set E := Equiv.ofBijective (extendByLast f) hbij'
  refine ⟨d.reindex E.symm, hd.reindex _, ?_, ?_⟩
  · -- Old points: `P` is `p` read back along the inverse of the face.
    have he : Fin.castSuccEmb.trans E.symm.toEmbedding = F.symm.toEmbedding.trans Fin.castSuccEmb :=
      Function.Embedding.ext fun i ↦ by
        simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.coe_castSuccEmb]
        rw [Equiv.symm_apply_eq]
        change (i : Fin n).castSucc = extendByLast f (F.symm i).castSucc
        rw [extendByLast_castSucc]
        exact congrArg Fin.castSucc (F.apply_symm_apply i).symm
    have hP : p.reindex F.symm = P := by
      have h := map_reindex_restrictFace P f F.symm
      rw [hPf, Option.map_some] at h
      have hid : F.symm.toEmbedding.trans f = Function.Embedding.refl (Fin n) :=
        Function.Embedding.ext fun i ↦ F.apply_symm_apply i
      rw [hid, restrictFace_refl] at h
      exact Option.some_injective _ h
    rw [restrictFace_reindex, he, ← map_reindex_restrictFace, hdp, Option.map_some, hP]
  · -- The new face: `d` itself.
    have hid : (extendByLast f).trans E.symm.toEmbedding = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i ↦ E.symm_apply_apply i
    rw [restrictFace_reindex, hid, restrictFace_refl]

/-- **The empty chart.**  Every legal one-point stage type `d` whose face on no points is the face
of the empty chart `P` is, reindexed, a pinned extension of `P` exact over the empty face. -/
theorem exists_pinned_extension_of_isEmpty {P : StageType.{u} α 0} {p : StageType.{u} α 0}
    {d : StageType.{u} α 1} (hPf : restrictFace (Function.Embedding.refl (Fin 0)) P = some p)
    (hd : d.IsLegal) (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α 1, Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast (Function.Embedding.refl (Fin 0))) Q = some d :=
  exists_pinned_extension_of_surjective (fun y ↦ y.elim0) hPf hd hdp

/-! ### The exact pinned extension -/

/-- **The exact pinned extension** (row 6 of the table of Layer 3, 3.4), from the coatom extension
property.  For a legal stage type `P` at stage `α`, a closed face `f` of `P` with restriction `p`,
and a legal one-point coface `d` of `p`, there is a legal one-point pinned extension `Q` of `P`
whose face along `extendByLast f` is exactly `d`.  One coatom extension is used for each point of
`P` outside the face. -/
theorem exists_pinned_extension (hext : HasCoatomExtensions.{u} α) {P : StageType.{u} α n}
    (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)}
    (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d := by
  induction hk : n - m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    subst hk
    by_cases hsurj : Function.Surjective f
    · exact exists_pinned_extension_of_surjective hsurj hPf hd hdp
    -- A point `x` outside the face whose addition keeps the face closed (accessibility).
    have hfP : univ.map f ∈ P.toCellScheme.faces := ((restrictFace_eq_some_iff P f).mp hPf).1
    have hplan := P.isWellFormed.isWellFormed.isPlan
    rw [P.isWellFormed.ground_eq] at hplan
    have hne : univ.map f ≠ univ := fun he ↦ hsurj fun y ↦ by
      have hy : y ∈ univ.map f := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxP⟩ := hplan.exists_insert_mem hfP hne
    have hx' : x ∉ Set.range f := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set f' := Fin.Embedding.snoc f hx'
    -- `Fin.Embedding.init_snoc`, with `Fin.Embedding.init` unfolded.
    have hff' : Fin.castSuccEmb.trans f' = f := Fin.Embedding.init_snoc f hx'
    have hf'P : univ.map f' ∈ P.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    set p' := P.comap f' hf'P
    have hPf' : restrictFace f' P = some p' := restrictFace_of_mem P f' hf'P
    have hp' : p'.IsLegal := hP.restrictFace f' hPf'
    have hp'p : restrictFace Fin.castSuccEmb p' = some p := by
      rw [restrictFace_trans P f' _ hPf', hff', hPf]
    -- One coatom extension: amalgamate `p'` and `d` over `p`.
    obtain ⟨t, ht, htp', htd⟩ := hext m p' d p hp' hd hp'p hdp
    -- The remaining points: `t` is a one-point coface of the enlarged face `p'`.
    have hmn : m < n := by
      have hle : m ≤ n := by simpa using Fintype.card_le_of_embedding f
      refine lt_of_le_of_ne hle fun he ↦ hsurj ?_
      exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp [he]⟩).2
    obtain ⟨Q, hQ, hQP, hQt⟩ := ih (n - (m + 1)) (by omega) hPf' ht htp' rfl
    refine ⟨Q, hQ, hQP, ?_⟩
    rw [← hff', ← extendByLast_trans,
      ← restrictFace_trans Q _ _ hQt, htd]

/-! ### The face must be closed -/

/-- **The face must be closed.**  If a stage type `Q` restricts to `P` along `Fin.castSuccEmb`
and has a face along `extendByLast f`, then `f` spans a closed face of `P`. -/
theorem univ_map_mem_faces_of_isSome_restrictFace_extendByLast {Q : StageType.{u} α (n + 1)}
    {P : StageType.{u} α n} {f : Fin m ↪ Fin n} (hQP : restrictFace Fin.castSuccEmb Q = some P)
    (hQf : (restrictFace (extendByLast f) Q).isSome) : univ.map f ∈ P.toCellScheme.faces := by
  obtain ⟨hc, rfl⟩ := (restrictFace_eq_some_iff Q _).mp hQP
  have he := (isSome_restrictFace_iff Q _).mp hQf
  have hplan := Q.isWellFormed.isWellFormed.isPlan
  have hi := hplan.infClosed hc he
  have hmeet : univ.map Fin.castSuccEmb ⊓ univ.map (extendByLast f) =
      (univ.map f).map Fin.castSuccEmb := by
    rw [inf_eq_inter, univ_map_extendByLast, inter_insert_of_notMem (by simp),
      inter_eq_right.mpr (map_subset_map.mpr (subset_univ _))]
  rw [mem_coe, hmeet] at hi
  exact (Scheme.mem_comap_faces _ _).mpr hi

/-! ### Stage types on no points -/

/-- A stage type on no points has no cells: a cell would have a positive grade at most the size of
its scope, which is empty. -/
theorem card_eq_zero (t : StageType.{u} α 0) : t.card = 0 := by
  by_contra h
  have d : Fin t.card := ⟨0, Nat.pos_of_ne_zero h⟩
  have hle := t.isWellFormed.isWellFormed.grade_le_card d
  have hpos := t.isWellFormed.isWellFormed.grade_pos d
  have hs : t.toCellScheme.scope d = ∅ := eq_empty_of_isEmpty _
  rw [hs, card_empty] at hle
  omega

/-- The faces of a stage type on no points: only the empty face. -/
theorem faces_eq_of_zero (t : StageType.{u} α 0) : t.toCellScheme.faces = {∅} := by
  ext C
  simp only [mem_singleton]
  refine ⟨fun _ ↦ eq_empty_of_isEmpty C, ?_⟩
  rintro rfl
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

/-- **There is only one stage type on no points** at each stage. -/
theorem eq_of_zero (t t' : StageType.{u} α 0) : t = t' := by
  have hc := t.card_eq_zero
  have hc' := t'.card_eq_zero
  refine ext (Scheme.ext (hc.trans hc'.symm) (by rw [t.isWellFormed.ground_eq,
    t'.isWellFormed.ground_eq]) (by rw [t.faces_eq_of_zero, t'.faces_eq_of_zero])
    (fun i ↦ (hc ▸ i).elim0) (fun i ↦ (hc ▸ i).elim0) (fun s ↦ (hc ▸ s).elim0))
    fun i ↦ (hc ▸ i).elim0

/-- The empty face of a stage type is defined. -/
theorem isSome_restrictFace_of_zero (t : StageType.{u} α n) (e : Fin 0 ↪ Fin n) :
    (restrictFace e t).isSome := by
  rw [isSome_restrictFace_iff, univ_eq_empty, map_empty]
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

/-! ### Amalgamation -/

/-- **One-point extension** [Kni26, Proposition 4.3.23], from the coatom extension property:
every legal stage type at stage `α` is the face along `Fin.castSuccEmb` of a legal stage type on
one more point.  This is the exact pinned extension over the empty face, with the new point
carrying the legal one-point stage type of the one-point scheme (`Scheme.isLegal_onePoint`); any
other legal one-point stage type can be prescribed there by `exists_pinned_extension`. -/
theorem exists_extension (hext : HasCoatomExtensions.{u} α) {P : StageType.{u} α n}
    (hP : P.IsLegal) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P := by
  set d := Scheme.isLegal_onePoint.{u}.toStageType α
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (d.isSome_restrictFace_of_zero Fin.castSuccEmb)
  obtain ⟨Q, hQ, hQP, -⟩ := exists_pinned_extension hext hP hp
    (Scheme.isLegal_onePoint.isLegal_toStageType α) (hp'.trans (congrArg some (eq_of_zero p' p)))
  exact ⟨Q, hQ, hQP⟩

/-- **Amalgamation over a common face**, from the coatom extension property: two legal stage types
`P` and `R` whose faces along `f` and `g` are the same stage type `p` are the faces of one legal
stage type, along embeddings `i` and `j` with `i ∘ f = j ∘ g`.  The points of `R` outside the face
are added one at a time, each by an exact pinned extension. -/
theorem exists_amalgam (hext : HasCoatomExtensions.{u} α) {P : StageType.{u} α n}
    {R : StageType.{u} α k} (hP : P.IsLegal) (hR : R.IsLegal) {f : Fin m ↪ Fin n}
    {g : Fin m ↪ Fin k} {p : StageType.{u} α m} (hPf : restrictFace f P = some p)
    (hRg : restrictFace g R = some p) :
    ∃ (N : ℕ) (Q : StageType.{u} α N) (i : Fin n ↪ Fin N) (j : Fin k ↪ Fin N), Q.IsLegal ∧
      restrictFace i Q = some P ∧ restrictFace j Q = some R ∧ f.trans i = g.trans j := by
  induction hk : k - m using Nat.strong_induction_on generalizing n m P f with
  | _ l ih =>
    subst hk
    by_cases hsurj : Function.Surjective g
    · -- `R` is its face `p`, read back along the inverse of `g`.
      set G := Equiv.ofBijective g ⟨g.injective, hsurj⟩
      have hRp : p.reindex G.symm = R := by
        have h := map_reindex_restrictFace R g G.symm
        rw [hRg, Option.map_some] at h
        have hid : G.symm.toEmbedding.trans g = Function.Embedding.refl (Fin k) :=
          Function.Embedding.ext fun i ↦ G.apply_symm_apply i
        rw [hid, restrictFace_refl] at h
        exact Option.some_injective _ h
      refine ⟨n, P, Function.Embedding.refl _, G.symm.toEmbedding.trans f, hP, restrictFace_refl P,
        ?_, ?_⟩
      · rw [← map_reindex_restrictFace, hPf, Option.map_some, hRp]
      · exact Function.Embedding.ext fun i ↦ congrArg f (G.symm_apply_apply i).symm
    -- A point `x` of `R` outside the face whose addition keeps the face closed.
    have hgR : univ.map g ∈ R.toCellScheme.faces := ((restrictFace_eq_some_iff R g).mp hRg).1
    have hplan := R.isWellFormed.isWellFormed.isPlan
    rw [R.isWellFormed.ground_eq] at hplan
    have hne : univ.map g ≠ univ := fun he ↦ hsurj fun y ↦ by
      have hy : y ∈ univ.map g := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxR⟩ := hplan.exists_insert_mem hgR hne
    have hx' : x ∉ Set.range g := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set g' := Fin.Embedding.snoc g hx'
    -- `Fin.Embedding.init_snoc`, with `Fin.Embedding.init` unfolded.
    have hgg' : Fin.castSuccEmb.trans g' = g := Fin.Embedding.init_snoc g hx'
    have hg'R : univ.map g' ∈ R.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    have hRg' : restrictFace g' R = some (R.comap g' hg'R) := restrictFace_of_mem R g' hg'R
    have hp'p : restrictFace Fin.castSuccEmb (R.comap g' hg'R) = some p := by
      rw [restrictFace_trans R g' _ hRg', hgg', hRg]
    -- Extend `P` over its face `f` by the enlarged face of `R`.
    obtain ⟨P', hP', hP'P, hP'f⟩ :=
      exists_pinned_extension hext hP hPf (hR.restrictFace g' hRg') hp'p
    have hmk : m < k := by
      have hle : m ≤ k := by simpa using Fintype.card_le_of_embedding g
      refine lt_of_le_of_ne hle fun he ↦ hsurj ?_
      exact ((Fintype.bijective_iff_injective_and_card g).mpr ⟨g.injective, by simp [he]⟩).2
    obtain ⟨N, Q, i', j, hQ, hQP', hQR, hij⟩ :=
      ih (k - (m + 1)) (by omega) hP' hP'f hRg' rfl
    refine ⟨N, Q, Fin.castSuccEmb.trans i', j, hQ, ?_, hQR, ?_⟩
    · rw [← restrictFace_trans Q i' _ hQP', hP'P]
    · have h := congrArg (Fin.castSuccEmb.trans ·) hij
      rw [← Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc,
        castSuccEmb_trans_extendByLast, hgg'] at h
      rw [← h, Function.Embedding.trans_assoc]

end StageType

end VaughtConjecture

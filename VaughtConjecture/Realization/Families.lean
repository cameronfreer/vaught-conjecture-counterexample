/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Cap
import VaughtConjecture.Stage.Legal

/-!
# The four extension families

Roadmap, Layer 2 (the four unchanged extension families); semantic contract, item 5 (the
general-family, bottom-pattern, uniform-band, and high-grade-dominance requirements demand some
suitable coface, not every prescribed one).

The **cofaces** of a stage type `p` on `n` points (`StageType.cofaces p`) are the legal stage types
`q` on `n + 1` points whose face along the initial segment `Fin.castSuccEmb : Fin n ↪ Fin (n + 1)`
is defined and equal to `p`.  The existential-closure clause of a model asks, over an occurrence of
type `p`, for a new point whose extended tuple has a type in one of four families of stage types
on `n + 1` points, each intersected with the cofaces of `p`:

* **generalized saturation** (`saturationFamily S`): the types with scheme `S`;
* **bottom pattern** (`bottomPatternFamily S ρ`): the types with scheme `S` which, on the cells of
  grade at most `n`, are bottom exactly where the labelling `ρ` of the cells of `S` is bottom;
* **uniformity** (`uniformityFamily γ`): the types with a label in the band `[γ, γ + ω)`;
* **high-arity dominance** (`dominanceFamily γ`): the types with a label above `γ` at a cell of
  grade `n + 1` (the arity of a cell is its grade).

**Side conditions.**  In the source, generalized saturation ranges over the legal schemes `S` on
`n + 1` points whose face along the initial segment is the scheme of `p`, and the bottom pattern
additionally over the lawful sections `ρ` of `S` (with no stage bound) that extend the labels of
`p`.  At a stage that is zero or a limit these side conditions are exactly the nonemptiness of
`cofaces p ∩ saturationFamily S` (`nonempty_cofaces_inter_saturationFamily_iff`), and a
bottom-pattern instance is nonempty exactly when its family is that of a section satisfying the
side conditions (`nonempty_cofaces_inter_bottomPatternFamily_iff`: the labels of any member are
such a section).  The side conditions make both families nonempty, as in [Kni26, Lemma 4.4.4]:

* a lawful section extending `p` reduces to a coface with the same bottom pattern
  (`ofIsLawful_mem_cofaces`, `nonempty_cofaces_inter_bottomPatternFamily`);
* bountifulness of `S` extends the labels of `p` to a lawful section of `S`, at the cap `⊥`
  (`exists_isLawful_extend_label`, `nonempty_cofaces_inter_saturationFamily`).

The corresponding nonemptiness of the uniformity and dominance instances at limit stages
([Kni26, Lemmas 4.4.2 and 4.4.3], by amalgamation through [Kni26, Corollary 4.3.22], with
[Kni26, Lemma 4.2.2] for the seed) is not proved here; the three lemmas together give
[Kni26, Lemma 4.4.1].

**Transport.**  Along a bijection `e` of the `n + 1` points that maps the initial segment to itself
by `σ`, cofaces of `p` reindex to cofaces of `p.reindex σ` (`reindex_mem_cofaces`), and the
families reindex with their parameters; the uniformity and dominance families are invariant under
every reindexing (`reindex_mem_uniformityFamily_iff`, `reindex_mem_dominanceFamily_iff`).  A
bijection fixing the initial segment pointwise is the identity, so the literal invariance under
such bijections says nothing.  Dominance families shrink as `γ` grows (`dominanceFamily_anti`);
uniformity families for different `γ` that are zero or limits are not comparable, since the bands
`[γ, γ + ω)` of distinct such `γ` are disjoint.  Every
bottom-pattern family lies in the saturation family of its scheme
(`bottomPatternFamily_subset_saturationFamily`).

**Reduction.**  Stage reduction to `β` sends cofaces to cofaces (`reduce_mem_cofaces`), preserves
the saturation, bottom-pattern, and dominance families, and preserves the uniformity family for
`γ < β` when `β` is zero or a limit (`reduce_mem_uniformityFamily`).  Stage reduction is itself the
construction `ofIsLawful` applied to the labels of a type (`reduce_eq_ofIsLawful`).  In the other
direction, a coface at `β` of the reduction of `p` lifts to a coface of `p` at a zero-or-limit
stage `α ≥ β` with the same scheme and the same capped observation at any cap `c ≤ β` that is
self-visible at the top grade (`exists_isLawful_lift`, `ofIsLawful_mem_cofaces_of_lift`):
bountifulness of the coface's scheme lifts the labels of `p` against the labels of the coface, and
the result is reduced to stage `α`.  This lifting serves the reduction of the guarded
generalized-saturation and bottom-pattern clauses of a model.

## References

The cofaces and the four families are the sets `U ⊆ (S^α ι_{n,n+1})⁻¹(p)` of clause 4 of
[Kni26, Definition 3.2.1]: (a)i generalized saturation, (a)ii the bottom pattern, (b) uniformity,
and (c) high-arity dominance.  That every instance is nonempty is [Kni26, Lemma 4.4.1], proved
there through [Kni26, Lemmas 4.4.2–4.4.4]; bountifulness is [Kni26, Definition 2.5.14] and the
stage reduction of types is [Kni26, Definition 3.1.2], for R. W. Knight, *A counterexample to
Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ}

/-! ### Cofaces and the four families -/

/-- The **cofaces** of a stage type `p` on `n` points [Kni26, Definition 3.2.1]: the legal stage
types on `n + 1` points whose face along the initial segment is `p`. -/
def cofaces (p : StageType.{u} α n) : Set (StageType.{u} α (n + 1)) :=
  {q | q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p}

/-- **Generalized saturation** [Kni26, Definition 3.2.1, clause 4(a)i]: the stage types on
`n + 1` points with scheme `S`. -/
def saturationFamily (S : Scheme.{u} (n + 1)) : Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S}

/-- The **bottom pattern** [Kni26, Definition 3.2.1, clause 4(a)ii]: the stage types on `n + 1`
points with scheme `S` whose labels on the cells of grade at most `n` are bottom exactly where
the labelling `ρ` of the cells of `S` is bottom. -/
def bottomPatternFamily (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}) :
    Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S ∧ ∀ (i : Fin q.card) (j : Fin S.card), (i : ℕ) = j →
    q.toCellScheme.grade i ≤ n → (q.label i = ⊥ ↔ ρ j = ⊥)}

/-- **Uniformity** [Kni26, Definition 3.2.1, clause 4(b)]: the stage types on `n + 1` points with
a label in the band `[γ, γ + ω)`.  The clause of a model uses it for every `γ` that is zero or a
limit and below the stage. -/
def uniformityFamily (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ d, (γ : Label.{u}) ≤ q.label d ∧ q.label d < ((γ + Ordinal.omega0 : Ordinal.{u}) : Label)}

/-- **High-arity dominance** [Kni26, Definition 3.2.1, clause 4(c)]: the stage types on `n + 1`
points with a label above `γ` at a cell of grade `n + 1`.  The clause of a model uses it for
`γ` below the stage. -/
def dominanceFamily (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ d, q.toCellScheme.grade d = n + 1 ∧ (γ : Label.{u}) < q.label d}

variable {p : StageType.{u} α n} {q : StageType.{u} α (n + 1)} {S : Scheme.{u} (n + 1)}
  {ρ : Fin S.card → Label.{u}}

/-- Membership in the cofaces: legality and the face along the initial segment. -/
@[simp] theorem mem_cofaces :
    q ∈ p.cofaces ↔ q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p :=
  Iff.rfl

/-- Membership in the saturation family: the scheme. -/
@[simp] theorem mem_saturationFamily : q ∈ saturationFamily S ↔ q.toScheme = S := Iff.rfl

/-- Membership in the bottom-pattern family: the scheme and the bottom pattern on the cells of
grade at most `n`. -/
theorem mem_bottomPatternFamily : q ∈ bottomPatternFamily S ρ ↔ q.toScheme = S ∧
    ∀ (i : Fin q.card) (j : Fin S.card), (i : ℕ) = j → q.toCellScheme.grade i ≤ n →
      (q.label i = ⊥ ↔ ρ j = ⊥) :=
  Iff.rfl

/-- Membership in the uniformity family: a label in the band `[γ, γ + ω)`. -/
theorem mem_uniformityFamily : q ∈ uniformityFamily γ ↔
    ∃ d, (γ : Label.{u}) ≤ q.label d ∧ q.label d < ((γ + Ordinal.omega0 : Ordinal.{u}) : Label) :=
  Iff.rfl

/-- Membership in the dominance family: a label above `γ` at a cell of grade `n + 1`. -/
theorem mem_dominanceFamily :
    q ∈ dominanceFamily γ ↔ ∃ d, q.toCellScheme.grade d = n + 1 ∧ (γ : Label.{u}) < q.label d :=
  Iff.rfl

/-- The type whose cofaces are taken is legal. -/
theorem IsLegal.of_mem_cofaces (hq : q ∈ p.cofaces) : p.IsLegal :=
  hq.1.restrictFace _ hq.2

/-- A coface of `p` restricts along the initial segment to the scheme of `p`. -/
theorem comap_toScheme_of_mem_cofaces (hq : q ∈ p.cofaces) :
    q.toScheme.comap Fin.castSuccEmb = p.toScheme := by
  obtain ⟨hf, h⟩ := (restrictFace_eq_some_iff _ _).mp hq.2
  exact congrArg toScheme h

/-- The initial segment is a closed face of every coface. -/
theorem castSucc_mem_faces_of_mem_cofaces (hq : q ∈ p.cofaces) :
    univ.map Fin.castSuccEmb ∈ q.toCellScheme.faces :=
  (isSome_restrictFace_iff _ _).mp (by rw [hq.2]; rfl)

/-- Every bottom-pattern family lies in the saturation family of its scheme. -/
theorem bottomPatternFamily_subset_saturationFamily :
    bottomPatternFamily S ρ ⊆ (saturationFamily S : Set (StageType.{u} α (n + 1))) :=
  fun _ h ↦ h.1

/-- Dominance families shrink as `γ` grows. -/
theorem dominanceFamily_anti {γ γ' : Ordinal.{u}} (h : γ ≤ γ') :
    (dominanceFamily γ' : Set (StageType.{u} α (n + 1))) ⊆ dominanceFamily γ :=
  fun _ ⟨d, hg, hd⟩ ↦ ⟨d, hg, lt_of_le_of_lt (by simpa using h) hd⟩

/-! ### Reindexing -/

section Reindex

variable (e : Fin (n + 1) ≃ Fin (n + 1))

/-- Reindexing along a bijection of the points keeps every cell: the cell map is surjective. -/
theorem surjective_cellMap_equiv (t : StageType.{u} α (n + 1)) :
    Function.Surjective (t.cellMap e.toEmbedding) :=
  t.toScheme.surjective_cellMap_equiv e

/-- **Cofaces reindex**: along a bijection `e` of the `n + 1` points mapping the initial segment
to itself by `σ`, a coface of `p` reindexes to a coface of `p.reindex σ`. -/
theorem reindex_mem_cofaces {σ : Fin n ≃ Fin n}
    (he : ∀ i, e (Fin.castSucc i) = Fin.castSucc (σ i)) (hq : q ∈ p.cofaces) :
    q.reindex e ∈ (p.reindex σ).cofaces := by
  refine ⟨hq.1.reindex e, ?_⟩
  have hcomp : Fin.castSuccEmb.trans e.toEmbedding = σ.toEmbedding.trans Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simpa using he i
  rw [restrictFace_reindex, hcomp, ← map_reindex_restrictFace, hq.2, Option.map_some]

/-- The saturation family reindexes with its scheme. -/
theorem reindex_mem_saturationFamily (hq : q ∈ saturationFamily S) :
    q.reindex e ∈ saturationFamily (S.comap e.toEmbedding) := by
  subst hq
  rfl

/-- The bottom-pattern family reindexes with its scheme and pattern. -/
theorem reindex_mem_bottomPatternFamily (hq : q ∈ bottomPatternFamily S ρ) :
    q.reindex e ∈ bottomPatternFamily (S.comap e.toEmbedding) (ρ ∘ S.cellMap e.toEmbedding) := by
  obtain ⟨rfl, hq⟩ := hq
  refine ⟨rfl, fun i j hij hg ↦ ?_⟩
  obtain rfl := Fin.ext hij
  exact hq _ _ rfl hg

/-- The uniformity family is invariant under reindexing. -/
@[simp] theorem reindex_mem_uniformityFamily_iff :
    q.reindex e ∈ uniformityFamily γ ↔ q ∈ uniformityFamily γ := by
  refine ⟨fun ⟨d, hd⟩ ↦ ⟨_, hd⟩, fun ⟨d, hd⟩ ↦ ?_⟩
  obtain ⟨i, rfl⟩ := surjective_cellMap_equiv e q d
  exact ⟨i, hd⟩

/-- The dominance family is invariant under reindexing. -/
@[simp] theorem reindex_mem_dominanceFamily_iff :
    q.reindex e ∈ dominanceFamily γ ↔ q ∈ dominanceFamily γ := by
  refine ⟨fun ⟨d, hd⟩ ↦ ⟨_, hd⟩, fun ⟨d, hd⟩ ↦ ?_⟩
  obtain ⟨i, rfl⟩ := surjective_cellMap_equiv e q d
  exact ⟨i, hd⟩

end Reindex

/-! ### Stage reduction of the families -/

section Reduce

variable (hβ : Order.IsSuccPrelimit β)

/-- Stage reduction sends cofaces of `p` to cofaces of the reduction of `p`. -/
theorem reduce_mem_cofaces (hq : q ∈ p.cofaces) : q.reduce hβ ∈ (p.reduce hβ).cofaces :=
  ⟨hq.1.reduce hβ, by rw [restrictFace_reduce, hq.2, Option.map_some]⟩

/-- Stage reduction keeps the saturation family. -/
theorem reduce_mem_saturationFamily (hq : q ∈ saturationFamily S) :
    q.reduce hβ ∈ saturationFamily S :=
  hq

/-- Stage reduction keeps the bottom-pattern family. -/
theorem reduce_mem_bottomPatternFamily (hq : q ∈ bottomPatternFamily S ρ) :
    q.reduce hβ ∈ bottomPatternFamily S ρ :=
  ⟨hq.1, fun i j hij hg ↦ reduce_eq_bot_iff.trans (hq.2 i j hij hg)⟩

/-- Stage reduction to a stage `β` that is zero or a limit keeps the uniformity family for
`γ < β`: the band `[γ, γ + ω)` lies below `β`. -/
theorem reduce_mem_uniformityFamily (hγ : γ < β) (hq : q ∈ uniformityFamily γ) :
    q.reduce hβ ∈ uniformityFamily γ := by
  obtain ⟨d, hγd, hdγ⟩ := hq
  have hlt : q.label d < β := by
    induction h : q.label d using recBotCoeTop with
    | bot => exact WithBot.bot_lt_coe _
    | coe o =>
      rw [h] at hdγ
      exact_mod_cast (show o < γ + Ordinal.omega0 by exact_mod_cast hdγ).trans_le
        (Ordinal.add_omega0_le_of_isSuccPrelimit hβ hγ)
    | top => exact absurd (h ▸ hdγ) (not_lt.mpr le_top)
  exact ⟨d, by simpa [reduce_of_lt hlt] using hγd, by simpa [reduce_of_lt hlt] using hdγ⟩

/-- Stage reduction keeps the dominance family: it never lowers a label. -/
theorem reduce_mem_dominanceFamily (hq : q ∈ dominanceFamily γ) :
    q.reduce hβ ∈ dominanceFamily γ := by
  obtain ⟨d, hg, hd⟩ := hq
  exact ⟨d, hg, hd.trans_le (le_reduce β _)⟩

end Reduce

/-! ### The side conditions give nonempty families -/

section Nonempty

variable {S : Scheme.{u} (n + 1)} {p : StageType.{u} α n}

/-- A lawful section of a legal scheme extending the labels of `p` along the initial segment
gives, at a zero-or-limit stage, a coface of `p`. -/
theorem ofIsLawful_mem_cofaces (hα : Order.IsSuccPrelimit α) (hS : S.IsLegal)
    (hf : univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces)
    (hp : S.comap Fin.castSuccEmb = p.toScheme) {ρ : Fin S.card → Label.{u}}
    (hρ : S.rows.IsLawful ρ)
    (hext : ∀ (i : Fin (S.comap Fin.castSuccEmb).card) (j : Fin p.card), (i : ℕ) = j →
      ρ (S.cellMap Fin.castSuccEmb i) = p.label j) :
    ofIsLawful hα S hS.isWellFormed hS.isCoded ρ hρ ∈ p.cofaces :=
  ⟨hS, restrictFace_ofIsLawful hα hf hp hext⟩

/-- **Nonempty bottom-pattern families** [Kni26, Lemma 4.4.4], the instance of [Kni26, Lemma 4.4.1]
for [Kni26, Definition 3.2.1, clause 4(a)ii]: at a stage that is zero or a limit, for a legal
scheme `S` extending the scheme of `p` and a lawful section `ρ` of `S` extending the labels of `p`
(with no stage bound), some coface of `p` has the bottom pattern of `ρ`. -/
theorem nonempty_cofaces_inter_bottomPatternFamily (hα : Order.IsSuccPrelimit α) (hS : S.IsLegal)
    (hf : univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces)
    (hp : S.comap Fin.castSuccEmb = p.toScheme) {ρ : Fin S.card → Label.{u}}
    (hρ : S.rows.IsLawful ρ)
    (hext : ∀ (i : Fin (S.comap Fin.castSuccEmb).card) (j : Fin p.card), (i : ℕ) = j →
      ρ (S.cellMap Fin.castSuccEmb i) = p.label j) :
    (p.cofaces ∩ bottomPatternFamily S ρ).Nonempty :=
  ⟨_, ofIsLawful_mem_cofaces hα hS hf hp hρ hext, rfl, fun i j hij _ ↦ by
    rw [Fin.ext hij]
    simp⟩

/-- **Nonempty saturation families**, the instance of [Kni26, Lemma 4.4.1] for
[Kni26, Definition 3.2.1, clause 4(a)i]: at a stage that is zero or a limit, for a legal scheme
`S` on `n + 1` points whose face along the initial segment is the scheme of `p`, some coface of
`p` has scheme `S`.  As in [Kni26, Lemma 4.4.4], applied to a lawful section of `S` extending the
labels of `p`, which bountifulness provides. -/
theorem nonempty_cofaces_inter_saturationFamily (hα : Order.IsSuccPrelimit α) (hS : S.IsLegal)
    (hf : univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces)
    (hp : S.comap Fin.castSuccEmb = p.toScheme) :
    (p.cofaces ∩ saturationFamily S).Nonempty := by
  obtain ⟨ρ, hρ, hext⟩ := exists_isLawful_extend_label hS hf hp
  obtain ⟨q, hq, hqS, -⟩ := nonempty_cofaces_inter_bottomPatternFamily hα hS hf hp hρ hext
  exact ⟨q, hq, hqS⟩

/-- **The side conditions of generalized saturation**: at a stage that is zero or a limit, some
coface of `p` has scheme `S` exactly when `S` is legal, the initial segment is a closed face of
`S`, and the face of `S` there is the scheme of `p`. -/
theorem nonempty_cofaces_inter_saturationFamily_iff (hα : Order.IsSuccPrelimit α) :
    (p.cofaces ∩ saturationFamily S).Nonempty ↔ S.IsLegal ∧
      univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces ∧ S.comap Fin.castSuccEmb = p.toScheme := by
  refine ⟨fun ⟨q, hq, hS⟩ ↦ ?_, fun ⟨hS, hf, hp⟩ ↦
    nonempty_cofaces_inter_saturationFamily hα hS hf hp⟩
  subst hS
  exact ⟨hq.1, castSucc_mem_faces_of_mem_cofaces hq, comap_toScheme_of_mem_cofaces hq⟩

/-- **The side conditions of the bottom pattern**: at a stage that is zero or a limit, some coface
of `p` has the bottom pattern of `ρ` on `S` exactly when `S` satisfies the side conditions of
generalized saturation and the family is that of a lawful section of `S` extending the labels of
`p`.  Forward, the labels of any member are such a section. -/
theorem nonempty_cofaces_inter_bottomPatternFamily_iff (hα : Order.IsSuccPrelimit α)
    {ρ : Fin S.card → Label.{u}} :
    (p.cofaces ∩ bottomPatternFamily S ρ).Nonempty ↔ S.IsLegal ∧
      univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces ∧ S.comap Fin.castSuccEmb = p.toScheme ∧
      ∃ ρ' : Fin S.card → Label.{u}, S.rows.IsLawful ρ' ∧
        (∀ (i : Fin (S.comap Fin.castSuccEmb).card) (j : Fin p.card), (i : ℕ) = j →
          ρ' (S.cellMap Fin.castSuccEmb i) = p.label j) ∧
        (bottomPatternFamily S ρ' : Set (StageType.{u} α (n + 1))) = bottomPatternFamily S ρ := by
  refine ⟨fun ⟨q, hq, hS, hpat⟩ ↦ ?_, fun ⟨hS, hf, hp, ρ', hρ', hext, he⟩ ↦
    he ▸ nonempty_cofaces_inter_bottomPatternFamily hα hS hf hp hρ' hext⟩
  subst hS
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff _ _).mp hq.2
  refine ⟨hq.1, hf, comap_toScheme_of_mem_cofaces hq, q.label, q.isLawful,
    fun i j hij ↦ label_congr hqp hij, Set.ext fun r ↦ ?_⟩
  have hgr {s t : Scheme.{u} (n + 1)} (h : s = t) {i : Fin s.card} {j : Fin t.card}
      (hij : (i : ℕ) = j) : s.toCellScheme.grade i = t.toCellScheme.grade j := by
    subst h
    rw [Fin.ext hij]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun i j hij hg ↦ ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, fun i j hij hg ↦ ?_⟩⟩
  · rw [h2 i j hij hg, ← hpat j j rfl (hgr h1 hij ▸ hg)]
  · rw [h2 i j hij hg, hpat j j rfl (hgr h1 hij ▸ hg)]

end Nonempty

/-! ### Lifting cofaces along stage reduction -/

section Lift

/-- The lift of a coface of `p.reduce hβ`, at a zero-or-limit stage `α`, is a coface of `p`. -/
theorem ofIsLawful_mem_cofaces_of_lift (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccPrelimit β)
    {p : StageType.{u} α n} {q' : StageType.{u} β (n + 1)} (hq' : q' ∈ (p.reduce hβ).cofaces)
    {ρ : Fin q'.card → Label.{u}} (hρ : q'.rows.IsLawful ρ)
    (hext : ∀ (i : Fin (q'.toScheme.comap Fin.castSuccEmb).card) (j : Fin p.card), (i : ℕ) = j →
      ρ (q'.cellMap Fin.castSuccEmb i) = p.label j) :
    ofIsLawful hα q'.toScheme q'.isWellFormed q'.isCoded ρ hρ ∈ p.cofaces :=
  ofIsLawful_mem_cofaces hα hq'.1 (castSucc_mem_faces_of_mem_cofaces hq')
    (comap_toScheme_of_mem_cofaces hq') hρ hext

end Lift

end StageType

end VaughtConjecture

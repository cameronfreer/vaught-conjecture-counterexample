/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Legal

/-!
# The four extension families

Roadmap, Layer 2 (the four unchanged extension families); semantic contract, item 5 (the
general-family, bottom-pattern, uniformity, and high-arity-dominance clauses demand some
suitable coface, not every prescribed one).

The **cofaces** of a stage type `p` on `n` points (`StageType.cofaces p`) are the legal stage types
`q` on `n + 1` points whose face along the initial segment `Fin.castSuccEmb : Fin n ↪ Fin (n + 1)`
is defined and equal to `p`.  The existential-closure clause of a model asks, over an occurrence of
type `p`, for a new point whose extended tuple has a type in one of four families of stage types
on `n + 1` points, each intersected with the cofaces of `p`:

* **generalized saturation** (`saturationFamily S`): the types with scheme `S`;
* **bottom pattern** (`bottomPatternFamily S ρ`): the types with scheme `S` which, on the cells of
  grade at most `n`, are bottom exactly where the labelling `ρ` of the cells of `S` is bottom;
* **uniformity** (`uniformityFamily γ`): the types with a label in `[γ, γ + ω)` (a block when `γ`
  is zero or a limit);
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
[Kni26, Lemma 4.2.2] for the seed) is not proved here; it is in
`VaughtConjecture.Extension.FamilyCofaces`, under the coatom extension property (uniformity) and
its form with apex (dominance).  The three lemmas together give [Kni26, Lemma 4.4.1].  The
uniformity and dominance instances, with the amalgam of a legal stage type and a legal stage type
on one point over the empty face, are bundled as the statement `HasNonemptyCofaceInstances α` used
by the cap-to-model theorem and by the empty-root case of receiving.

**Receiving.**  The receiving family of a stage type `d` at a cutoff `c` (`receivingFamily d c`)
consists of the stage types on the scheme of `d` with the observation of `d` at `c`; it contains
`d` (`self_mem_receivingFamily`), and membership is transitive (`mem_receivingFamily_trans`),
passes to lower cutoffs (`mem_receivingFamily_of_le`), and reindexes
(`reindex_mem_receivingFamily`); faces of its members are members of the receiving families of the
faces (`exists_restrictFace_mem_receivingFamily`), and a stage type on the scheme of `d` that
equals `d` at every cell not labelled the formal top and exceeds `γ` at every other cell is in the
receiving family of `d` at the cutoff `γ` (`mem_receivingFamily_of_capped`).  **Repair**: if the
face of a legal `D` along `f` is `p'`, and `p` agrees with `p'` at a cap `c ≤ α` self-visible at
the arity of `D`, then at a zero-or-limit stage `α` some legal `d` has face `p` along `f` literally
and agrees with `D` at `c` (`exists_restrictFace_eq_mem_receivingFamily`): bountifulness of the
scheme of `D` extends the labels of `p` to a lawful section with the observation of `D` at `c`
(`exists_isLawful_extend_of_mem_receivingFamily`).  The bottom-pattern family of a labelling
depends on the labelling only through which of its values are bottom
(`bottomPatternFamily_congr`).

**Transport.**  Along a bijection `e` of the `n + 1` points that maps the initial segment to itself
by `σ`, cofaces of `p` reindex to cofaces of `p.reindex σ` (`reindex_mem_cofaces`), and the
families reindex with their parameters; the uniformity and dominance families are invariant under
every reindexing (`reindex_mem_uniformityFamily_iff`, `reindex_mem_dominanceFamily_iff`).  A
bijection fixing the initial segment pointwise is the identity, so the literal invariance under
such bijections says nothing.  Dominance families shrink as `γ` grows (`dominanceFamily_anti`);
the blocks `[γ, γ + ω)` of distinct `γ` that are zero or limits are disjoint, though membership in
a uniformity family is existential over the cells, so this alone does not compare the uniformity
families for distinct such `γ`.  Every bottom-pattern family lies in the saturation family of
its scheme (`bottomPatternFamily_subset_saturationFamily`).

**Reduction.**  Stage reduction to `β` sends cofaces to cofaces (`reduce_mem_cofaces`), preserves
the saturation, bottom-pattern, and dominance families, and preserves the uniformity family for
`γ < β` when `β` is zero or a limit (`reduce_mem_uniformityFamily`).  Stage reduction is itself the
construction `ofIsLawful` applied to the labels of a type (`reduce_eq_ofIsLawful`).  Read
backwards, a type is in a bottom-pattern family exactly when its reduction is
(`reduce_mem_bottomPatternFamily_iff`), and a type whose reduction to `β` is in the uniformity or
dominance family of `γ < β` is in it (`mem_uniformityFamily_of_reduce`,
`mem_dominanceFamily_of_reduce`).  In the other direction, a coface at `β` of the reduction of `p`
lifts to a coface of `p` at a zero-or-limit stage `α ≥ β` with the same scheme and the same capped
observation at any cap `c ≤ β` that is self-visible at the top grade (`exists_isLawful_lift`,
`ofIsLawful_mem_cofaces_of_lift`): bountifulness of the coface's scheme lifts the labels of `p`
against the labels of the coface, and the result is reduced to stage `α`.  This lifting is used in
the reduction of the guarded generalized-saturation and bottom-pattern clauses of a model.

**No lower bound at full grade.**  Relabelling every cell of full grade `⊥` (`botTopGrade`) keeps
a type in its saturation and bottom-pattern families and among the cofaces of its face, so every
nonempty instance of either family has a member labelled `⊥` at every cell of full grade
(`exists_mem_cofaces_inter_saturationFamily_label_eq_bot`,
`exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot`), hence a member in no dominance
family (`exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily`).  **Availability from
the face**: in a legal coface `q` of `p`, every cell of `p` has a cell of `q` of full scope and the
same grade labelled at least as high (`exists_le_label_of_restrictFace`).

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
a label in `[γ, γ + ω)`.  The clause of a model uses it for every `γ` that is zero or a limit and
below the stage, where the interval is a block. -/
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

/-- Membership in the uniformity family: a label in `[γ, γ + ω)`. -/
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

/-- The bottom-pattern family of a labelling depends only on which of its values are bottom. -/
theorem bottomPatternFamily_congr {S : Scheme.{u} (n + 1)} {ρ ρ' : Fin S.card → Label.{u}}
    (h : ∀ j, ρ j = ⊥ ↔ ρ' j = ⊥) :
    (bottomPatternFamily S ρ : Set (StageType.{u} α (n + 1))) = bottomPatternFamily S ρ' := by
  ext q
  simp only [mem_bottomPatternFamily, h]

/-- Dominance families shrink as `γ` grows. -/
theorem dominanceFamily_anti {γ γ' : Ordinal.{u}} (h : γ ≤ γ') :
    (dominanceFamily γ' : Set (StageType.{u} α (n + 1))) ⊆ dominanceFamily γ :=
  fun _ ⟨d, hg, hd⟩ ↦ ⟨d, hg, lt_of_le_of_lt (by simpa using h) hd⟩

/-! ### The receiving family -/

/-- The **receiving family** of a stage type `d` at a cutoff `c`: the stage types on the scheme of
`d` with the observation of `d` at `c`. -/
def receivingFamily (d : StageType.{u} α n) (c : Label.{u}) : Set (StageType.{u} α n) :=
  {q | q.toScheme = d.toScheme ∧
    ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → min (q.label i) c = min (d.label j) c}

/-- Membership in the receiving family: the scheme and the observation at the cutoff. -/
theorem mem_receivingFamily {d q : StageType.{u} α n} {c : Label.{u}} :
    q ∈ receivingFamily d c ↔ q.toScheme = d.toScheme ∧
      ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → min (q.label i) c = min (d.label j) c :=
  Iff.rfl

/-- A stage type is in each of its receiving families. -/
theorem self_mem_receivingFamily (d : StageType.{u} α n) (c : Label.{u}) :
    d ∈ receivingFamily d c :=
  ⟨rfl, fun _ _ h ↦ by rw [Fin.ext h]⟩

/-- Agreement at a cap gives agreement at every lower cap. -/
theorem mem_receivingFamily_of_le {D q : StageType.{u} α n} {c c' : Label.{u}}
    (hq : q ∈ receivingFamily D c') (h : c ≤ c') : q ∈ receivingFamily D c :=
  ⟨hq.1, fun i j hij ↦ by
    simpa only [min_assoc, min_eq_right h] using congrArg (min · c) (hq.2 i j hij)⟩

/-- Receiving families at one cutoff compose: agreement at `c` is transitive. -/
theorem mem_receivingFamily_trans {D d q : StageType.{u} α n} {c : Label.{u}}
    (hq : q ∈ receivingFamily d c) (hd : d ∈ receivingFamily D c) : q ∈ receivingFamily D c := by
  refine ⟨hq.1.trans hd.1, fun i j hij ↦ ?_⟩
  have hk : (i : ℕ) < d.card := i.2.trans_eq (congrArg Scheme.card hq.1)
  exact (hq.2 i ⟨i, hk⟩ rfl).trans (hd.2 ⟨i, hk⟩ j hij)

/-- Receiving families reindex: along a bijection `e` of points, a member of the receiving family
of `D` reindexes to a member of the receiving family of `D.reindex e`. -/
theorem reindex_mem_receivingFamily {D q : StageType.{u} α n} {c : Label.{u}} (e : Fin m ≃ Fin n)
    (hq : q ∈ receivingFamily D c) : q.reindex e ∈ receivingFamily (D.reindex e) c := by
  obtain ⟨hS, hl⟩ := hq
  obtain ⟨S, ℓ, _, _, _, _⟩ := q
  obtain ⟨S', ℓ', _, _, _, _⟩ := D
  obtain rfl : S = S' := hS
  refine ⟨rfl, fun i j hij ↦ ?_⟩
  obtain rfl := Fin.ext hij
  exact hl _ _ rfl

/-- **Faces of members of a receiving family**: if `Q` is in the receiving family of `D` at `c`,
then along every face at which `D` restricts to `d`, `Q` restricts to a member of the receiving
family of `d` at `c`. -/
theorem exists_restrictFace_mem_receivingFamily {D Q : StageType.{u} α n} {c : Label.{u}}
    (hQ : Q ∈ receivingFamily D c) {f : Fin m ↪ Fin n} {d : StageType.{u} α m}
    (hd : restrictFace f D = some d) :
    ∃ q, restrictFace f Q = some q ∧ q ∈ receivingFamily d c := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp hd
  obtain ⟨hS, hl⟩ := hQ
  obtain ⟨S, ℓ, _, _, _, _⟩ := Q
  obtain ⟨S', ℓ', _, _, _, _⟩ := D
  obtain rfl : S = S' := hS
  refine ⟨_, restrictFace_of_mem _ f (by exact hf), rfl, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := Fin.ext hij
  exact hl _ _ rfl

/-- **Capped agreement gives receiving**: a stage type on the scheme of `D` that equals `D` at
every cell where `D` is not the formal top and exceeds `γ` at every cell where `D` is the formal
top is in the receiving family of `D` at the cutoff `γ`. -/
theorem mem_receivingFamily_of_capped {D Q : StageType.{u} α n} {γ : Ordinal.{u}}
    (hS : Q.toScheme = D.toScheme)
    (h : ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
      (D.label j ≠ ⊤ → Q.label i = D.label j) ∧ (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)) :
    Q ∈ receivingFamily D γ := by
  refine ⟨hS, fun i j hij ↦ ?_⟩
  by_cases hD : D.label j = ⊤
  · rw [hD, min_eq_right ((h i j hij).2 hD).le, min_eq_right le_top]
  · rw [(h i j hij).1 hD]

/-! ### Repairing a donor to a received face

A **received face** is a stage type `p` that agrees at a cap with the face `p'` of a donor `D`
along `f`, as the type of a tuple received for that face does; the repair replaces `D` by a legal
`d` whose face along `f` is `p` literally. -/

section Repair

/-- **Repairing a donor to a received face.**  If the face of a legal `D` along `f` is `p'`, and
`p` agrees with `p'` at a cap `c` self-visible at `n`, the labels of `p` extend along `f` to a
lawful section of the scheme of `D` with the observation of `D` at `c`.  This is bountifulness of
the scheme of `D` (`Scheme.IsLegal.exists_isLawful_extend`); when `p = p'` it is
`exists_isLawful_lift` at the stage of `D`. -/
theorem exists_isLawful_extend_of_mem_receivingFamily {f : Fin m ↪ Fin n}
    {D : StageType.{u} α n} {p' p : StageType.{u} α m} (hD : D.IsLegal)
    (hface : restrictFace f D = some p') {c : Label.{u}} (hc : IsSelfVisible n c)
    (hp : p ∈ receivingFamily p' c) :
    ∃ ρ : Fin D.card → Label.{u}, D.rows.IsLawful ρ ∧ (∀ d, min (ρ d) c = min (D.label d) c) ∧
      ∀ (i : Fin (D.toScheme.comap f).card) (j : Fin p.card), (i : ℕ) = j →
        ρ (D.cellMap f i) = p.label j := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hface
  obtain ⟨hpS, hpl⟩ := hp
  obtain ⟨P, ℓ, hw, hcod, hℓ, hat⟩ := p
  obtain rfl : P = D.toScheme.comap f := hpS
  obtain ⟨ρ, hρ, hρc, hext⟩ := Scheme.IsLegal.exists_isLawful_extend hD hf hc hℓ D.isLawful
    fun i ↦ (hpl i i rfl).symm
  exact ⟨ρ, hρ, hρc, fun i j hij ↦ by rw [hext, Fin.ext hij]⟩

/-- **The repaired donor**: at a zero-or-limit stage, a legal `D` whose face along `f` agrees
with `p` at a cap `c ≤ α` self-visible at `n` is replaced by a legal `d` whose face along `f` is
`p` literally and which agrees with `D` at `c`.  The labels of `d` are the stage reduction of the
section of `exists_isLawful_extend_of_mem_receivingFamily`; reduction may raise a label at or
above `α` to the formal top, which does not change the observation at `c`. -/
theorem exists_restrictFace_eq_mem_receivingFamily (hα : Order.IsSuccPrelimit α)
    {f : Fin m ↪ Fin n} {D : StageType.{u} α n} {p' p : StageType.{u} α m} (hD : D.IsLegal)
    (hface : restrictFace f D = some p') {c : Label.{u}} (hc : IsSelfVisible n c) (hcα : c ≤ α)
    (hp : p ∈ receivingFamily p' c) :
    ∃ d : StageType.{u} α n, d.IsLegal ∧ restrictFace f d = some p ∧ d ∈ receivingFamily D c := by
  obtain ⟨ρ, hρ, hρc, hext⟩ := exists_isLawful_extend_of_mem_receivingFamily hD hface hc hp
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hface
  refine ⟨ofIsLawful hα D.toScheme D.isWellFormed D.isCoded ρ hρ, hD,
    restrictFace_ofIsLawful hα hf hp.1.symm hext, rfl, fun i j hij ↦ ?_⟩
  obtain rfl := Fin.ext hij
  exact (min_reduce_of_le hcα (ρ i)).trans (hρc i)

end Repair

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
`γ < β`: the interval `[γ, γ + ω)` lies below `β`. -/
theorem reduce_mem_uniformityFamily (hγ : γ < β) (hq : q ∈ uniformityFamily γ) :
    q.reduce hβ ∈ uniformityFamily γ := by
  obtain ⟨d, hγd, hdγ⟩ := hq
  have hlt : q.label d < β :=
    hdγ.trans_le (by exact_mod_cast Ordinal.add_omega0_le_of_isSuccPrelimit hβ hγ)
  exact ⟨d, by simpa [reduce_of_lt hlt] using hγd, by simpa [reduce_of_lt hlt] using hdγ⟩

/-- Stage reduction keeps the dominance family: it never lowers a label. -/
theorem reduce_mem_dominanceFamily (hq : q ∈ dominanceFamily γ) :
    q.reduce hβ ∈ dominanceFamily γ := by
  obtain ⟨d, hg, hd⟩ := hq
  exact ⟨d, hg, hd.trans_le (le_reduce β _)⟩

end Reduce

/-! ### Stage reduction of the families, read backwards

Conversely, membership of a stage reduction in a family gives membership of the type, for the
bottom-pattern family at every stage and for the uniformity and dominance families of `γ < β`. -/

section ReduceBackwards

/-- A type is in a bottom-pattern family exactly when its stage reduction is: reduction keeps
the scheme and the bottom labels. -/
theorem reduce_mem_bottomPatternFamily_iff (hβ : Order.IsSuccPrelimit β)
    {S : Scheme.{u} (n + 1)} {ρ : Fin S.card → Label.{u}} :
    q.reduce hβ ∈ bottomPatternFamily S ρ ↔ q ∈ bottomPatternFamily S ρ :=
  ⟨fun h ↦ ⟨h.1, fun i j hij hg ↦ reduce_eq_bot_iff.symm.trans (h.2 i j hij hg)⟩,
    reduce_mem_bottomPatternFamily hβ⟩

/-- A type whose stage reduction to `β` is in the uniformity family of `γ < β` is in it: the
interval `[γ, γ + ω)` lies below `β`, where reduction changes no label. -/
theorem mem_uniformityFamily_of_reduce (hβ : Order.IsSuccPrelimit β) (hγ : γ < β)
    (h : q.reduce hβ ∈ uniformityFamily γ) : q ∈ uniformityFamily γ := by
  obtain ⟨d, hγd, hdγ⟩ := h
  -- the labels of `q.reduce hβ` are, by definition, the reductions of the labels of `q`
  change (γ : Label.{u}) ≤ Label.reduce β (q.label d) at hγd
  change Label.reduce β (q.label d) < ((γ + Ordinal.omega0 : Ordinal.{u}) : Label.{u}) at hdγ
  have hlt : Label.reduce β (q.label d) < β :=
    hdγ.trans_le (by exact_mod_cast Ordinal.add_omega0_le_of_isSuccPrelimit hβ hγ)
  rw [reduce_lt_iff] at hlt
  rw [reduce_of_lt hlt] at hγd hdγ
  exact ⟨d, hγd, hdγ⟩

/-- A type whose stage reduction to `β` is in the dominance family of `γ < β` is in it: a label
that reduction raises to the formal top is at least `β`, hence above `γ`. -/
theorem mem_dominanceFamily_of_reduce (hβ : Order.IsSuccPrelimit β) (hγ : γ < β)
    (h : q.reduce hβ ∈ dominanceFamily γ) : q ∈ dominanceFamily γ := by
  obtain ⟨d, hg, hd⟩ := h
  -- the labels of `q.reduce hβ` are, by definition, the reductions of the labels of `q`
  change (γ : Label.{u}) < Label.reduce β (q.label d) at hd
  refine ⟨d, hg, ?_⟩
  by_cases hlt : q.label d < β
  · rwa [reduce_of_lt hlt] at hd
  · exact (show (γ : Label.{u}) < β by exact_mod_cast hγ).trans_le (not_lt.mp hlt)

end ReduceBackwards

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

/-! ### Nonempty coface instances -/

variable (α) in
/-- **Nonempty coface instances** at a stage `α`: the three statements about legal stage types at
`α` used by the cap-to-model theorem at `α` and by the empty-root case of receiving.  Each follows
from the coatom extension property with apex at `α`
(`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`, in
`VaughtConjecture.Extension.FamilyCofaces`). -/
structure HasNonemptyCofaceInstances : Prop where
  /-- **The amalgam over the empty face**: a legal stage type `P` on `n` points and a legal stage
  type `d` on one point are the faces, along the first `n` points and along the last point, of
  one coface of `P`. -/
  exists_amalgam_empty ⦃n : ℕ⦄ (P : StageType.{u} α n) (d : StageType.{u} α 1) :
    P.IsLegal → d.IsLegal → ∃ Q ∈ P.cofaces, restrictFace (Fin.natAddEmb n) Q = some d
  /-- **Uniformity instances**: for `γ` zero or a limit below `α`, some coface of a legal stage
  type has a label in `[γ, γ + ω)`. -/
  uniformity ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u},
    Order.IsSuccPrelimit γ → γ < α → (p.cofaces ∩ uniformityFamily γ).Nonempty
  /-- **Dominance instances**: for `γ` below `α`, some coface of a legal stage type on `n` points
  has a label above `γ` at a cell of grade `n + 1`. -/
  dominance ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u}, γ < α →
    (p.cofaces ∩ dominanceFamily γ).Nonempty

/-! ### Saturation gives no lower bound on a label of full grade -/

/-- The stage type `q` with every cell of full grade relabelled `⊥`; lawful by
`CellScheme.Rows.IsLawful.capTopGrade` at the cap `⊥`. -/
noncomputable def botTopGrade (q : StageType.{u} α (n + 1)) : StageType.{u} α (n + 1) where
  toScheme := q.toScheme
  label i := if q.toCellScheme.grade i = n + 1 then ⊥ else q.label i
  isWellFormed := q.isWellFormed
  isCoded := q.isCoded
  isLawful := by
    simpa only [min_bot_right] using
      q.isLawful.capTopGrade q.grade_le (isSelfVisible_bot (n + 1))
  atStage i := by
    split_ifs
    · exact atStage_bot
    · exact q.atStage i

/-- Below full grade the labels of `botTopGrade` are those of `q`. -/
theorem botTopGrade_label_of_grade_le (q : StageType.{u} α (n + 1)) {i : Fin q.card}
    (hi : q.toCellScheme.grade i ≤ n) : q.botTopGrade.label i = q.label i := by
  -- `botTopGrade` labels by an `if` on the grade (by definition)
  change (if _ then _ else _) = _
  split_ifs with h
  · omega
  · rfl

/-- At full grade `botTopGrade` is labelled `⊥`. -/
theorem botTopGrade_label_of_grade_eq (q : StageType.{u} α (n + 1)) {i : Fin q.card}
    (hi : q.toCellScheme.grade i = n + 1) : q.botTopGrade.label i = ⊥ := by
  -- `botTopGrade` labels by an `if` on the grade (by definition)
  change (if _ then _ else _) = _
  split_ifs
  rfl

/-- Relabelling the cells of full grade `⊥` does not change the face along the initial segment. -/
theorem restrictFace_castSuccEmb_botTopGrade (q : StageType.{u} α (n + 1)) :
    restrictFace Fin.castSuccEmb q.botTopGrade = restrictFace Fin.castSuccEmb q := by
  by_cases hf : univ.map Fin.castSuccEmb ∈ q.toCellScheme.faces
  · rw [restrictFace_of_mem q.botTopGrade Fin.castSuccEmb hf, restrictFace_of_mem q _ hf]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    have hgr : q.toCellScheme.grade (q.cellMap Fin.castSuccEmb i) ≤ n := by
      have h := congrArg Prod.snd (q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i)
      exact h.symm.trans_le ((q.comap Fin.castSuccEmb hf).grade_le i)
    simp only [comap_label]
    rw [Fin.ext hij] at hgr ⊢
    exact q.botTopGrade_label_of_grade_le hgr
  · rw [restrictFace_of_notMem q.botTopGrade Fin.castSuccEmb hf, restrictFace_of_notMem q _ hf]

/-- **The bottom-pattern clause bounds no label of full grade from below**: every nonempty
instance of the bottom-pattern family among the cofaces of `p` has a member whose cells of full
grade are all labelled `⊥` (`botTopGrade`: the face and the bottom pattern below full grade are
unchanged). -/
theorem exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot {p : StageType.{u} α n}
    {S : Scheme.{u} (n + 1)} {ρ : Fin S.card → Label.{u}}
    (h : (p.cofaces ∩ bottomPatternFamily S ρ).Nonempty) :
    ∃ q ∈ p.cofaces ∩ bottomPatternFamily S ρ,
      ∀ i, q.toCellScheme.grade i = n + 1 → q.label i = ⊥ := by
  obtain ⟨q, ⟨hq, hqp⟩, hqS, hpat⟩ := h
  refine ⟨q.botTopGrade, ⟨⟨hq, (restrictFace_castSuccEmb_botTopGrade q).trans hqp⟩, hqS,
    fun i j hij hi ↦ ?_⟩, fun i ↦ q.botTopGrade_label_of_grade_eq⟩
  rw [q.botTopGrade_label_of_grade_le hi]
  exact hpat i j hij hi

/-- **The saturation clause bounds no label of full grade from below**: every nonempty instance
of generalized saturation among the cofaces of `p` has a member whose cells of full grade are all
labelled `⊥`. -/
theorem exists_mem_cofaces_inter_saturationFamily_label_eq_bot {p : StageType.{u} α n}
    {S : Scheme.{u} (n + 1)} (h : (p.cofaces ∩ saturationFamily S).Nonempty) :
    ∃ q ∈ p.cofaces ∩ saturationFamily S,
      ∀ i, q.toCellScheme.grade i = n + 1 → q.label i = ⊥ := by
  obtain ⟨q, hq, hqS⟩ := h
  exact ⟨q.botTopGrade, ⟨⟨hq.1, (restrictFace_castSuccEmb_botTopGrade q).trans hq.2⟩, hqS⟩,
    fun i ↦ q.botTopGrade_label_of_grade_eq⟩

/-- **A prescribed scheme does not meet a dominance family by force**: every nonempty instance of
generalized saturation among the cofaces of `p` has a member in no dominance family.  So no clause
of a model asks for a coface on a prescribed scheme with a label of full grade above a floor. -/
theorem exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily
    {p : StageType.{u} α n} {S : Scheme.{u} (n + 1)}
    (h : (p.cofaces ∩ saturationFamily S).Nonempty) :
    ∃ q ∈ p.cofaces ∩ saturationFamily S, ∀ γ : Ordinal.{u}, q ∉ dominanceFamily γ := by
  obtain ⟨q, hq, hbot⟩ := exists_mem_cofaces_inter_saturationFamily_label_eq_bot h
  refine ⟨q, hq, fun γ ⟨i, hi, hγi⟩ ↦ ?_⟩
  rw [hbot i hi] at hγi
  exact not_lt_bot hγi

/-! ### Availability from the face -/

/-- **Availability from the face**: in a legal stage type `q` on `n + 1` points whose face along
the initial segment is `p`, every cell `T` of `p` has a cell of `q` of full scope, with the grade
of `T`, labelled at least as `T`. -/
theorem exists_le_label_of_restrictFace {p : StageType.{u} α n} {q : StageType.{u} α (n + 1)}
    (hq : q.IsLegal) (h : restrictFace Fin.castSuccEmb q = some p) (T : Fin p.card) :
    ∃ G : Fin q.card, q.toCellScheme.gradedIndex G = (univ, p.toCellScheme.grade T) ∧
      p.label T ≤ q.label G := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp h
  have hgi := q.toScheme.map_comap_gradedIndex Fin.castSuccEmb T
  have hgr : q.toCellScheme.grade (q.cellMap Fin.castSuccEmb T) =
      (q.comap Fin.castSuccEmb hf).toCellScheme.grade T := (congrArg Prod.snd hgi).symm
  obtain ⟨t, ht⟩ := hq.isComplete (univ, (q.comap Fin.castSuccEmb hf).toCellScheme.grade T)
    ⟨q.univ_mem_faces, (q.comap Fin.castSuccEmb hf).isWellFormed.isWellFormed.grade_pos T,
      ((q.comap Fin.castSuccEmb hf).grade_le T).trans (by simp)⟩
  obtain ⟨G, hG, hle⟩ := q.isLawful.availability (q.cellMap Fin.castSuccEmb T) t
    (by rw [show q.toCellScheme.scope t = univ from congrArg Prod.fst ht]; exact subset_univ _)
    (by rw [hgr, show q.toCellScheme.grade t = _ from congrArg Prod.snd ht])
  exact ⟨G, hG.trans ht, hle⟩

end StageType

end VaughtConjecture

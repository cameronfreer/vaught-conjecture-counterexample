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
uniformity families for different `γ` are not comparable, since their bands are disjoint.  Every
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

## Placement

`Scheme.IsLegal.exists_isLawful_extend`, `StageType.exists_isLawful_extend_label`, and
`StageType.exists_isLawful_lift` belong in `VaughtConjecture.Stage.Legal`, beside
`StageType.cappedLift_of_restrictFace`; `StageType.label_congr`, `StageType.ofIsLawful`, its
`simp` lemmas, `StageType.restrictFace_ofIsLawful`, and `StageType.reduce_eq_ofIsLawful` in
`VaughtConjecture.Stage.Basic`, where `StageType.reduce` can then be defined through
`StageType.ofIsLawful`; `StageType.surjective_cellMap_equiv`, a general reindexing fact, in
`VaughtConjecture.Stage.Scheme`, which holds `Scheme.cellMap`, stated there for schemes;
`Ordinal.add_omega0_le_of_isSuccPrelimit` in `VaughtConjecture.Label.OrdinalVisibility`, under
`Ordinal`, and `Label.exists_lt_lt_isSelfVisible` in `VaughtConjecture.Label.Visibility`.  They
are stated here so that those files are unchanged.  Moving
`Ordinal.add_omega0_le_of_isSuccPrelimit` requires amending the implementation note of
`VaughtConjecture.Label.OrdinalVisibility`, which admits in the root `Ordinal` namespace only
names containing `visibilityReplace` (for dot notation on ordinals) and
`Ordinal.lt_iff_mul_lt_of_dvd` with its `ω` case: the note would list it as a general ordinal fact
and
a candidate for Mathlib.

## References

The cofaces and the four families are the sets `U ⊆ (S^α ι_{n,n+1})⁻¹(p)` of clause 4 of
[Kni26, Definition 3.2.1]: (a)i generalized saturation, (a)ii the bottom pattern, (b) uniformity,
and (c) high-arity dominance.  That every instance is nonempty is [Kni26, Lemma 4.4.1], proved
there through [Kni26, Lemmas 4.4.2–4.4.4]; bountifulness is [Kni26, Definition 2.5.14] and the
stage reduction of types is [Kni26, Definition 3.1.2], for R. W. Knight, *A counterexample to
Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

/-! ### Bands below a limit -/

namespace Ordinal

/-- Below an ordinal `β` that is zero or a limit, the band `[γ, γ + ω)` of any `γ < β` lies below
`β`. -/
theorem add_omega0_le_of_isSuccPrelimit {β γ : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    (hγ : γ < β) : γ + ω ≤ β := by
  refine le_of_forall_lt fun o ho ↦ ?_
  obtain ⟨d, hd, hod⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).mp ho
  obtain ⟨k, rfl⟩ := lt_omega0.mp hd
  exact hod.trans (hβ.add_natCast_lt hγ k)

end Ordinal

namespace VaughtConjecture

open Finset Label

/-! ### Self-visible caps -/

namespace Label

variable {o β : Ordinal.{u}}

/-- **Self-visible caps.**  Between an ordinal `o` and a stage `β > o` that is zero or a limit
there is an ordinal self-visible at any given threshold `k`: `o + (k + 1)`. -/
theorem exists_lt_lt_isSelfVisible (hβ : Order.IsSuccPrelimit β) (ho : o < β) (k : ℕ) :
    ∃ c : Ordinal.{u}, o < c ∧ c < β ∧ IsSelfVisible k (c : Label.{u}) := by
  refine ⟨o + (k + 1 : ℕ), ?_, hβ.add_natCast_lt ho _, isSelfVisible_coe.mpr ?_⟩
  · exact lt_add_of_pos_right o (by exact_mod_cast k.succ_pos)
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o Ordinal.omega0_ne_zero)
  have hdecomp : o + (k + 1 : ℕ) = Ordinal.omega0 * (o / Ordinal.omega0) + (m + (k + 1) : ℕ) := by
    conv_lhs => rw [← Ordinal.div_add_mod o Ordinal.omega0]
    rw [hm, add_assoc]
    norm_cast
  rw [hdecomp, Ordinal.mul_add_mod_self, Ordinal.natCast_mod_omega0]
  exact_mod_cast (by omega : k ≤ m + (k + 1))

end Label

/-! ### Extending lawful labels from a closed face -/

namespace Scheme

variable {n m : ℕ} {S : Scheme.{u} n} {f : Fin m ↪ Fin n}

/-- **Extension from a closed face.**  Let `S` be legal and let the range of `f` be a closed face.
A lawful section `ℓ` of the restriction along `f` whose capped observation at a cap `c`
self-visible at `n` agrees with that of a lawful section `Q` of `S` on the face extends to a
lawful section of `S` with the capped observation of `Q` everywhere.  This is bountifulness of `S`
from the pair of the face to the pair `(univ, n)`, or the bottom end when `m = 0`. -/
theorem IsLegal.exists_isLawful_extend (hS : S.IsLegal) (hf : univ.map f ∈ S.toCellScheme.faces)
    {c : Label.{u}} (hc : IsSelfVisible n c) {ℓ : Fin (S.comap f).card → Label.{u}}
    (hℓ : (S.comap f).rows.IsLawful ℓ) {Q : Fin S.card → Label.{u}} (hQ : S.rows.IsLawful Q)
    (hQℓ : ∀ i, min (Q (S.cellMap f i)) c = min (ℓ i) c) :
    ∃ r : Fin S.card → Label.{u}, S.rows.IsLawful r ∧ (∀ d, min (r d) c = min (Q d) c) ∧
      ∀ i, r (S.cellMap f i) = ℓ i := by
  have hφ := S.isLowerEmbedding_comap f
  set X' : Finset (Fin m) × ℕ := (univ, m)
  set X : Finset (Fin n) × ℕ := (univ.map f, m)
  set Y : Finset (Fin n) × ℕ := (univ, n)
  have hX : S.cellMap f '' (S.comap f).toCellScheme.below X' = S.toCellScheme.below X :=
    S.image_cellMap_below f X'
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_embedding f
  have hXY : X ≤ Y := ⟨subset_univ _, hmn⟩
  have allE (i : Fin (S.comap f).card) : i ∈ (S.comap f).toCellScheme.below X' :=
    ⟨subset_univ _, ((hS.isWellFormed.comap f hf).isWellFormed.grade_le_card i).trans
      (by simpa using card_le_univ ((S.comap f).toCellScheme.scope i))⟩
  have allD (d : Fin S.card) : d ∈ S.toCellScheme.below Y :=
    ⟨subset_univ _, (hS.isWellFormed.isWellFormed.grade_le_card d).trans
      (by simpa using card_le_univ (S.toCellScheme.scope d))⟩
  have hl : S.rows.CappedLift hXY := by
    by_cases hm : m = 0
    · exact hS.isWellFormed.isWellFormed.cappedLift S.rows (Or.inl hm) hXY
    · exact hS.isBountiful.cappedLift ⟨hf, Nat.pos_of_ne_zero hm, by simp [X]⟩
        ⟨hS.isWellFormed.univ_mem_faces, show 0 < n by omega, by simp [Y]⟩ hXY
  set e := hφ.belowEquiv hX
  have he (i : Fin (S.comap f).card) : (e ⟨i, allE i⟩ : Fin S.card) = S.cellMap f i := rfl
  have hp : S.rows.IsLawfulBelow X fun d ↦ ℓ (e.symm d).1 := by
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ hX).mp ?_
    have h : ((fun d ↦ ℓ (e.symm d).1) ∘ e) = fun t ↦ ℓ t.1 := funext fun t ↦ by simp
    rw [h]
    exact hℓ.isLawfulBelow X'
  obtain ⟨q, hq, hqc, hqr⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp hl c hc _
    (fun d ↦ Q d.1) hp (hQ.isLawfulBelow Y) fun d ↦ by
      conv_lhs => rw [show (d : Fin S.card) = S.cellMap f (e.symm d).1 by
        rw [← he, Subtype.coe_eta, e.apply_symm_apply]]
      exact hQℓ _
  refine ⟨fun d ↦ q ⟨d, allD d⟩, hq.isLawful allD, fun d ↦ hqc _, fun i ↦ ?_⟩
  have := hqr ⟨S.cellMap f i, he i ▸ (e ⟨i, allE i⟩).2⟩
  simpa [show e.symm ⟨S.cellMap f i, _⟩ = ⟨i, allE i⟩ from
    e.symm_apply_eq.mpr (Subtype.ext (he i).symm)] using this

end Scheme

namespace StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ}

/-! ### Stage types from lawful sections -/

/-- Equal stage types have equal labels at cells with equal positions. -/
theorem label_congr {t t' : StageType.{u} α n} (h : t = t') {i : Fin t.card} {j : Fin t'.card}
    (hij : (i : ℕ) = j) : t.label i = t'.label j := by
  subst h
  rw [Fin.ext hij]

/-- The stage type at a zero-or-limit stage `α` on a well-formed scheme with coded rows, with the
stage reduction of a lawful section `ρ` as labels. -/
noncomputable def ofIsLawful (hα : Order.IsSuccPrelimit α) (S : Scheme.{u} n)
    (hw : S.IsWellFormed) (hc : S.IsCoded) (ρ : Fin S.card → Label.{u})
    (hρ : S.rows.IsLawful ρ) : StageType.{u} α n where
  toScheme := S
  label := Label.reduce α ∘ ρ
  isWellFormed := hw
  isCoded := hc
  isLawful := hρ.reduce hα
  atStage _ := atStage_reduce α _

section OfIsLawful

variable (hα : Order.IsSuccPrelimit α) (S : Scheme.{u} n) (hw : S.IsWellFormed) (hc : S.IsCoded)
  (ρ : Fin S.card → Label.{u}) (hρ : S.rows.IsLawful ρ)

/-- The scheme of `ofIsLawful` is the given scheme. -/
@[simp] theorem ofIsLawful_toScheme : (ofIsLawful hα S hw hc ρ hρ).toScheme = S := rfl

/-- The labels of `ofIsLawful` are the reduced labels of the section. -/
@[simp] theorem ofIsLawful_label (d : Fin S.card) :
    (ofIsLawful hα S hw hc ρ hρ).label d = Label.reduce α (ρ d) := rfl

variable {S hw hc ρ hρ}

/-- A stage type built from a lawful section extending the labels of `p` along a closed face has
the face `p` there. -/
theorem restrictFace_ofIsLawful {f : Fin m ↪ Fin n} (hf : univ.map f ∈ S.toCellScheme.faces)
    {p : StageType.{u} α m} (hp : S.comap f = p.toScheme)
    (hext : ∀ (i : Fin (S.comap f).card) (j : Fin p.card), (i : ℕ) = j →
      ρ (S.cellMap f i) = p.label j) :
    restrictFace f (ofIsLawful hα S hw hc ρ hρ) = some p := by
  rw [restrictFace_of_mem _ f hf]
  refine congrArg some (ext hp fun i j hij ↦ ?_)
  exact (congrArg (Label.reduce α) (hext i j hij)).trans (p.atStage j).reduce_eq

end OfIsLawful

/-- **Stage reduction through `ofIsLawful`**: the stage reduction of a type is `ofIsLawful`
applied to its own labels. -/
theorem reduce_eq_ofIsLawful (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n) :
    t.reduce hβ = ofIsLawful hβ t.toScheme t.isWellFormed t.isCoded t.label t.isLawful :=
  rfl

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
    Function.Surjective (t.cellMap e.toEmbedding) := fun d ↦ by
  have hd : d ∈ Set.range (t.cellMap e.toEmbedding) := by
    rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
    exact fun x _ ↦ ⟨e.symm x, by simp⟩
  exact hd

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

variable {f : Fin m ↪ Fin n} {S : Scheme.{u} n} {p : StageType.{u} α m}

/-- **Extension of the labels of a face**: if `S` is legal, the range of `f` is a closed face, and
the face of `S` there is the scheme of `p`, then the labels of `p` extend to a lawful section of
`S` (bountifulness at the cap `⊥`). -/
theorem exists_isLawful_extend_label (hS : S.IsLegal) (hf : univ.map f ∈ S.toCellScheme.faces)
    (hp : S.comap f = p.toScheme) : ∃ ρ : Fin S.card → Label.{u}, S.rows.IsLawful ρ ∧
      ∀ (i : Fin (S.comap f).card) (j : Fin p.card), (i : ℕ) = j →
        ρ (S.cellMap f i) = p.label j := by
  obtain ⟨P, ℓ, _, _, hℓ, _⟩ := p
  subst hp
  obtain ⟨ρ, hρ, -, hext⟩ := hS.exists_isLawful_extend hf (isSelfVisible_bot n) hℓ
    CellScheme.Rows.isLawful_bot fun _ ↦ by simp
  exact ⟨ρ, hρ, fun i j hij ↦ by rw [hext, Fin.ext hij]⟩

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

variable {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {q' : StageType.{u} β n} {c : Label.{u}}

/-- **Lifting a face across stage reduction.**  If a legal `q'` at stage `β` has, along `f`, the
face `p.reduce hβ`, then for a cap `c ≤ β` self-visible at `n` there is a lawful section of the
scheme of `q'` with the capped observation of `q'` at `c` that extends the labels of `p` along
`f`. -/
theorem exists_isLawful_lift (hβ : Order.IsSuccPrelimit β) (hq' : q'.IsLegal)
    (hface : restrictFace f q' = some (p.reduce hβ)) (hc : IsSelfVisible n c)
    (hcβ : c ≤ β) : ∃ ρ : Fin q'.card → Label.{u}, q'.rows.IsLawful ρ ∧
      (∀ d, min (ρ d) c = min (q'.label d) c) ∧
      ∀ (i : Fin (q'.toScheme.comap f).card) (j : Fin p.card), (i : ℕ) = j →
        ρ (q'.cellMap f i) = p.label j := by
  obtain ⟨hf, heq⟩ := (restrictFace_eq_some_iff _ _).mp hface
  obtain ⟨P, ℓ, hw, hcod, hℓ, hat⟩ := p
  have hP : q'.toScheme.comap f = P := congrArg toScheme heq
  subst hP
  obtain ⟨ρ, hρ, hρc, hext⟩ := Scheme.IsLegal.exists_isLawful_extend hq' hf hc hℓ q'.isLawful
    fun i ↦ (congrArg (min · c) (label_congr heq (i := i) (j := i) rfl)).trans
      (min_reduce_of_le hcβ _)
  exact ⟨ρ, hρ, hρc, fun i j hij ↦ by rw [hext, Fin.ext hij]⟩

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

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Cap
import VaughtConjecture.Stage.Bountiful
import VaughtConjecture.Stage.Countable

/-!
# Legal schemes and legal stage types

Roadmap, Layer 1 (countable stage types and exact partial face maps; stage-reduction coherence;
bountifulness); semantic contract, items 3–4; the expositions, §1–2.

A stage type (`StageType α n`) is the unrestricted structure: a well-formed scheme with coded rows
and a lawful label section at stage `α`.  Nothing forces its rows to be consistent, bountiful, or
complete.  The types of [Kni26, Definition 3.1.1] are built over a domain with its semantics
([Kni26, Definition 2.6.1]), whose semantics is coded, consistent, bountiful, and complete; this
is **legality**.  Definition 2.6.1 also asks that `⟨B,j⟩`, `P↾B`, `D⟨B,j⟩`, and `E⟨B,j⟩` be
recoverable from a cell; here that holds by representation (the rows are a field of the scheme),
and `Scheme.IsCoded` is only the range normalization of [Kni26, Lemma 2.5.13].

* `Scheme.IsLegal S`: the scheme is well formed, its rows are coded (`Scheme.IsCoded`),
  consistent (`CellScheme.Rows.IsConsistent`), and bountiful (`CellScheme.Rows.IsBountiful`), and
  it is complete (`CellScheme.IsComplete`).  Legality passes to the restriction to a closed face
  (`IsLegal.comap`) and to reindexing along a bijection of points (`IsLegal.reindex`).
* `StageType.IsLegal t`: the scheme of `t` is legal.  Since a stage type is already well formed
  with coded rows, this is consistency, bountifulness, and completeness (`StageType.isLegal_iff`).
  Legal stage types are closed under the face maps where defined (`IsLegal.restrictFace`),
  reindexing (`IsLegal.reindex`), and stage reduction (`isLegal_reduce_iff`); at a stage with
  countably many ordinals below it there are countably many of them on `n` points
  (`countable_setOf_isLegal`, from `StageType.countable`), the faithful form of
  [Kni26, Proposition 3.1.4].

**Reduction and the stage.**  `StageType.reduce` takes no bound relating the target stage `β` to
the stage `α` of the type.  For `β ≤ α` it is the reduction of [Kni26, Definition 3.1.2], whose
content is `StageType.reduce_label` with `Label.reduce_of_lt` (a label below `β` is kept) and
`Label.reduce_eq_top_iff` (a label at or above `β` becomes the formal top).  For `α ≤ β` it
changes no label (`StageType.reduce_label_of_le`) and only relabels the stage:
`t.reduce hβ = t.castLE hαβ` (`StageType.reduce_eq_castLE`, in `VaughtConjecture.Stage.Basic`),
where `castLE` reads a stage type at stage `α` as one at the larger stage `β`.  Relabelling is
invisible to reduction (`StageType.reduce_castLE`) and to legality (`isLegal_castLE_iff`).

**Lifting across a defined face.**  The restricted rows lift capped
(`CellScheme.Rows.CappedLift`) between two pairs exactly when the rows lift capped between their
images (`Scheme.cappedLift_comap_iff`, in `VaughtConjecture.Stage.Bountiful`).  In particular a
type whose face along `f` is defined and bountiful lifts capped between the images of the graded
faces of that face, with no assumption on its rows outside the face
(`StageType.cappedLift_of_restrictFace`).

**Extending lawful labels from a closed face.**  By bountifulness, a lawful section of the
restriction of a legal scheme to a closed face whose capped observation at a self-visible cap
agrees with that of a lawful section `Q` of the scheme extends to a lawful section with the
capped observation of `Q` (`Scheme.IsLegal.exists_isLawful_extend`).  At the cap `⊥` the labels
of a stage type on the face extend (`StageType.exists_isLawful_extend_label`); and if the face of
a legal `q'` at stage `β` is the reduction of `p`, the labels of `p` extend to a lawful section
with the capped observation of `q'` at a self-visible cap `c ≤ β`
(`StageType.exists_isLawful_lift`).

## References

Types are [Kni26, Definition 3.1.1], over the domains with their semantics of
[Kni26, Definition 2.6.1]; coding, consistency, bountifulness, and completeness of a semantics are
[Kni26, Lemma 2.5.13 and Definitions 2.5.12, 2.5.14, and 2.5.15]; stage reduction and the
restriction to a face of the plan are [Kni26, Definition 3.1.2], the preservation of the
laws under restriction is [Kni26, Lemma 2.5.5 and Proposition 2.6.3], and the countability of
the type spaces is [Kni26, Proposition 3.1.4].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Legal schemes -/

namespace Scheme

variable {n m : ℕ} (S : Scheme.{u} n) (f : Fin m ↪ Fin n)

/-- A scheme on `n` points is **legal**: it is well formed, and its rows are coded, consistent,
and bountiful, and it is complete; that is, it is a domain with a semantics as required for the
types of [Kni26, Definition 3.1.1].  The recoverability of `⟨B,j⟩`, `P↾B`, `D⟨B,j⟩`, and
`E⟨B,j⟩` from a cell in [Kni26, Definition 2.6.1] holds by representation (the rows are a field of
the scheme); `IsCoded` is only the range normalization of [Kni26, Lemma 2.5.13]. -/
structure IsLegal : Prop where
  /-- The scheme is well formed. -/
  isWellFormed : S.IsWellFormed
  /-- The rows are coded. -/
  isCoded : S.IsCoded
  /-- The rows are consistent. -/
  isConsistent : S.rows.IsConsistent
  /-- The rows are bountiful. -/
  isBountiful : S.rows.IsBountiful
  /-- Every graded face is the graded index of a cell. -/
  isComplete : S.toCellScheme.IsComplete

variable {S}

/-- **Restriction to a closed face** of a legal scheme is legal. -/
theorem IsLegal.comap (hS : S.IsLegal) (hf : univ.map f ∈ S.toCellScheme.faces) :
    (S.comap f).IsLegal where
  isWellFormed := hS.isWellFormed.comap f hf
  isCoded := hS.isCoded.comap f
  isConsistent := isConsistent_comap f hS.isConsistent
  isBountiful := isBountiful_comap f hS.isBountiful
  isComplete := isComplete_comap f hS.isComplete

/-- **Reindexing** a legal scheme along a bijection of points gives a legal scheme. -/
theorem IsLegal.reindex (hS : S.IsLegal) (e : Fin m ≃ Fin n) :
    (S.comap e.toEmbedding).IsLegal :=
  hS.comap _ (by simpa [map_univ_equiv] using hS.isWellFormed.univ_mem_faces)

end Scheme

/-! ### Legal stage types -/

namespace StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ} (t : StageType.{u} α n) (f : Fin m ↪ Fin n)

/-- A stage type is **legal** when its scheme is legal: its rows are consistent and bountiful and
its scheme is complete [Kni26, Definition 3.1.1].  A `StageType` alone is the unrestricted
structure. -/
def IsLegal : Prop := t.toScheme.IsLegal

variable {t}

/-- A stage type is legal exactly when its rows are consistent and bountiful and its scheme is
complete; well-formedness and coding are part of every stage type. -/
theorem isLegal_iff :
    t.IsLegal ↔ t.rows.IsConsistent ∧ t.rows.IsBountiful ∧ t.toCellScheme.IsComplete :=
  ⟨fun h ↦ ⟨h.isConsistent, h.isBountiful, h.isComplete⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨t.isWellFormed, t.isCoded, h₁, h₂, h₃⟩⟩

/-- The restriction of a legal stage type to a closed face is legal. -/
theorem IsLegal.comap (ht : t.IsLegal) (hf : univ.map f ∈ t.toCellScheme.faces) :
    (t.comap f hf).IsLegal :=
  Scheme.IsLegal.comap f ht hf

/-- **Face maps preserve legality**: a defined face of a legal stage type is legal. -/
theorem IsLegal.restrictFace (ht : t.IsLegal) {u : StageType.{u} α m}
    (hu : restrictFace f t = some u) : u.IsLegal := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact ht.comap f hf

/-- Reindexing a legal stage type along a bijection of points gives a legal stage type. -/
theorem IsLegal.reindex (ht : t.IsLegal) (e : Fin m ≃ Fin n) : (t.reindex e).IsLegal :=
  ht.comap _ _

/-- **Stage reduction preserves legality**: reduction keeps the scheme. -/
@[simp] theorem isLegal_reduce_iff (hβ : Order.IsSuccPrelimit β) :
    (t.reduce hβ).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-- Stage reduction of a legal stage type is legal. -/
theorem IsLegal.reduce (ht : t.IsLegal) (hβ : Order.IsSuccPrelimit β) : (t.reduce hβ).IsLegal :=
  ht

/-- **Countably many legal stage types**: if there are countably many ordinals below the stage
`α`, there are countably many legal stage types at stage `α` on `n` points.  This is the faithful
form of [Kni26, Proposition 3.1.4]: the type space at stage `α` on `n` points is the set of legal
stage types. -/
theorem countable_setOf_isLegal (hα : (Set.Iio α).Countable) (n : ℕ) :
    {t : StageType.{u} α n | t.IsLegal}.Countable :=
  have := StageType.countable hα n
  Set.to_countable _

/-! ### Relabelling the stage -/

variable (t)

/-- Relabelling the stage does not change legality. -/
@[simp] theorem isLegal_castLE_iff (h : α ≤ β) : (t.castLE h).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-! ### Capped lifting across a defined face -/

/-- **Lifting across a defined face.**  If the face map of `t` along `f` is defined with
bountiful rows, then the rows of `t` lift capped between the images of any two graded faces
`X ≤ Y` of that face.  Nothing is assumed about the rows of `t` outside the face. -/
theorem cappedLift_of_restrictFace {u : StageType.{u} α m} (hu : restrictFace f t = some u)
    (hb : u.rows.IsBountiful) {X Y : Finset (Fin m) × ℕ} (hX : X ∈ u.toCellScheme.gradedFaces)
    (hY : Y ∈ u.toCellScheme.gradedFaces) (h : X ≤ Y) :
    t.rows.CappedLift (X := Prod.map (Finset.map f) id X) (Y := Prod.map (Finset.map f) id Y)
      ⟨map_subset_map.mpr h.1, h.2⟩ := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact (t.toScheme.cappedLift_comap_iff f h).mp (hb.cappedLift hX hY h)

end StageType

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

variable {α β : Ordinal.{u}} {n m : ℕ}

section Extend

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
    CellScheme.Rows.isLawful_const_bot fun _ ↦ by simp
  exact ⟨ρ, hρ, fun i j hij ↦ by rw [hext, Fin.ext hij]⟩

end Extend

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

end Lift

end StageType

/-! ### Lawful sections of a face of a stage type -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ} {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
  {t : StageType.{u} α m}

/-- **Lawful sections of a face extend**: every lawful section of the rows of a face of a legal
stage type extends to a lawful section of its rows (bountifulness at the cap `⊥`,
`Scheme.IsLegal.exists_isLawful_extend`).  It concerns all lawful sections of the face, not only
its labels. -/
theorem exists_isLawful_extend_of_restrictFace (hD : D.IsLegal) (h : restrictFace f D = some t)
    {a : Fin t.card → Label.{u}} (ha : t.rows.IsLawful a) :
    ∃ a' : Fin D.card → Label.{u}, D.rows.IsLawful a' ∧ ∀ i, a' (faceCell h i) = a i := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  obtain ⟨r, hr, -, hext⟩ := Scheme.IsLegal.exists_isLawful_extend hD hf (isSelfVisible_bot n)
    ha D.isLawful fun _ ↦ by simp
  exact ⟨r, hr, fun i ↦ hext i⟩

end StageType

end VaughtConjecture

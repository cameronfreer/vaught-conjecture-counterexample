/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ClassRealization

/-!
# Coherent renaming of realizations

Numbering as in the current draft of [AFK26].  Native construction throughout.

**The face cell map.**  When the face of a stage type `p` along `f : Fin m ↪ Fin n` is defined,
`restrictFace f p = some p₀`, every cell of `p₀` names a cell of `p`: the cell map of the restricted
scheme (`Scheme.cellMap`), read on the cells of `p₀` (`StageType.faceCellMap`).

**Coherent renaming** (`Realization.CoherentRenaming R R'`).  For two realizations `R`, `R'` at the
same stage on the same carrier `M`:

* the same tuples are typed (`isSome_eval_iff`);
* at every tuple `t` typed by `p` in `R` and by `q` in `R'`, a renaming of cells
  [AFK26, Definition 4.6] (`renamingAt`, a `StageType.Renaming q p`): a bijection
  `σ t : Fin p.card ≃ Fin q.card` (`CoherentRenaming.cellEquiv`) with `p = q.renameCells (σ t)`,
  so that each cell `i` of `p` has the scope, the grade, the label and the row (read through
  `σ t`) of the cell `σ t i` of `q`, and `p`, `q` have the same plan
  (`CoherentRenaming.scope_eq`, `grade_eq`, `gradedIndex_eq`, `label_eq`, `row_eq`, `faces_eq`);
* **the family commutes with every face cell map** (`faceCellMap_comm`): for every `f` and `t` with
  `t` and `f.trans t` typed in both realizations, by `p, q` and `p₀, q₀`, and with the faces of
  `p, q` along `f` equal to `p₀, q₀`,
  `faceCellMap hfq ∘ σ (f.trans t) = σ t ∘ faceCellMap hfp`, where
  `hfp : restrictFace f p = some p₀` and `hfq : restrictFace f q = some q₀`.

The face equations `hfp`, `hfq` are part of the hypotheses of the commutation: a face cell map
exists only at a defined face.  For exactly consistent realizations they follow from the typing of
`t` and `f.trans t`, so the commutation is then asserted at every typed face of every typed tuple
(`CoherentRenaming.faceCellMap_cellEquiv_of_isConsistent`).

**Laws.**  Coherent renaming is reflexive and symmetric (`CoherentRenaming.refl`,
`CoherentRenaming.symm`), and transitive through an exactly consistent middle realization
(`CoherentRenaming.trans`): it is an equivalence relation on the exactly consistent realizations
(`Realization.isCoherentRenaming_equivalence`).  It reduces along stage reduction, with the same
bijections, for exactly consistent realizations (`CoherentRenaming.reduce`,
`CoherentRenaming.cellEquiv_reduce`).  It gives the tuplewise relation
`Realization.IsCellRenamingOf` (`CoherentRenaming.isCellRenamingOf`), hence equal class readings
(`Realization.classReading_eq_of_coherentRenaming`).  The converse is not claimed: tuplewise
renamings are chosen tuple by tuple with no compatibility along faces, and producing a coherent
family from them is the alignment target of
`VaughtConjecture.Correspondence.Presentation.Targets`.
-/

universe u v

namespace VaughtConjecture

open Finset

noncomputable section

namespace StageType

variable {α β : Ordinal.{u}} {n m : ℕ}

/-! ### The face cell map -/

/-- A defined face has the cells of the restricted scheme.  Native construction. -/
theorem card_eq_of_restrictFace_eq_some {p : StageType.{u} α n} {p₀ : StageType.{u} α m}
    {f : Fin m ↪ Fin n} (h : restrictFace f p = some p₀) :
    p₀.card = (p.toScheme.comap f).card := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff p f).mp h
  rfl

/-- **The face cell map** of a defined face `restrictFace f p = some p₀`: the cell of `p` named by
each cell of `p₀`, the cell map of the restricted scheme (`Scheme.cellMap`, the cells of `p`
visible through `f` in increasing order) read on the cells of `p₀`.  Native construction. -/
def faceCellMap {p : StageType.{u} α n} {p₀ : StageType.{u} α m} {f : Fin m ↪ Fin n}
    (h : restrictFace f p = some p₀) (i : Fin p₀.card) : Fin p.card :=
  p.cellMap f (Fin.cast (card_eq_of_restrictFace_eq_some h) i)

/-- At a closed face, the face cell map is the cell map.  Native construction. -/
@[simp] theorem faceCellMap_restrictFace_of_mem {p : StageType.{u} α n} {f : Fin m ↪ Fin n}
    (hf : univ.map f ∈ p.toCellScheme.faces) (i : Fin (p.comap f hf).card) :
    faceCellMap (restrictFace_of_mem p f hf) i = p.cellMap f i :=
  rfl

/-- The face cell map is injective.  Native construction. -/
theorem faceCellMap_injective {p : StageType.{u} α n} {p₀ : StageType.{u} α m}
    {f : Fin m ↪ Fin n} (h : restrictFace f p = some p₀) : Function.Injective (faceCellMap h) :=
  fun _ _ hij ↦ (Fin.cast_injective _) ((p.cellMap f).injective hij)

/-- Cell maps of equal schemes agree at equal positions. -/
private theorem val_cellMap_congr {S T : Scheme.{u} n} (h : S = T) (f : Fin m ↪ Fin n)
    {i : Fin (S.comap f).card} {j : Fin (T.comap f).card} (hij : (i : ℕ) = j) :
    (S.cellMap f i : ℕ) = T.cellMap f j := by
  subst h
  rw [Fin.ext hij]

/-- **The face cell map depends only on the scheme**: face cell maps of two stage types with the
same scheme agree at equal positions.  Native construction. -/
theorem val_faceCellMap_congr {p : StageType.{u} α n} {p₀ : StageType.{u} α m}
    {p' : StageType.{u} β n} {p₀' : StageType.{u} β m} {f : Fin m ↪ Fin n}
    (h : restrictFace f p = some p₀) (h' : restrictFace f p' = some p₀')
    (hs : p.toScheme = p'.toScheme) {i : Fin p₀.card} {i' : Fin p₀'.card}
    (hi : (i : ℕ) = i') : (faceCellMap h i : ℕ) = faceCellMap h' i' :=
  val_cellMap_congr hs f hi

/-! ### Renamings: data, composition and transport -/

namespace Renaming

variable {p q s : StageType.{u} α n}

/-- A renaming keeps the scope of every cell.  Native construction. -/
theorem scope_eq (r : p.Renaming q) (i : Fin q.card) :
    q.toCellScheme.scope i = p.toCellScheme.scope (r.toEquiv i) :=
  congrArg Prod.fst (r.gradedIndex_eq i)

/-- A renaming keeps the grade of every cell.  Native construction. -/
theorem grade_eq (r : p.Renaming q) (i : Fin q.card) :
    q.toCellScheme.grade i = p.toCellScheme.grade (r.toEquiv i) :=
  congrArg Prod.snd (r.gradedIndex_eq i)

/-- **A renaming keeps the rows**, read through the bijection: the row of the cell `i` at the cell
`e` below it is the row of `r.toEquiv i` at `r.toEquiv e`.  Native construction. -/
theorem row_eq (r : p.Renaming q) (i : Fin q.card)
    (e : q.toCellScheme.below (q.toCellScheme.gradedIndex i))
    (e' : p.toCellScheme.below (p.toCellScheme.gradedIndex (r.toEquiv i)))
    (he : e'.1 = r.toEquiv e.1) : q.rows.row i e = p.rows.row (r.toEquiv i) e' := by
  have key {k : ℕ} (τ : Fin k ≃ Fin p.card) (q' : StageType.{u} α n) (h : p.renameCells τ = q')
      (j : Fin k) (j' : Fin q'.card) (hj : (j : ℕ) = j') (x : Fin k)
      (x' : q'.toCellScheme.below (q'.toCellScheme.gradedIndex j')) (hx : (x : ℕ) = x'.1)
      (y : p.toCellScheme.below (p.toCellScheme.gradedIndex (τ j))) (hy : y.1 = τ x) :
      q'.rows.row j' x' = p.rows.row (τ j) y := by
    subst h
    obtain rfl := Fin.ext hj
    obtain rfl : x = x'.1 := Fin.ext hx
    exact p.rows.row_congr rfl hy.symm
  exact key r.toEquiv q r.renameCells_eq i i rfl e.1 e rfl e' he

/-- The identity renaming.  Native construction. -/
def refl (p : StageType.{u} α n) : p.Renaming p :=
  ⟨Equiv.refl _, rfl⟩

/-- The inverse renaming.  Native construction. -/
def symm (r : p.Renaming q) : q.Renaming p where
  toEquiv := r.toEquiv.symm
  renameCells_eq := by
    have key {k : ℕ} (τ : Fin k ≃ Fin p.card) (q' : StageType.{u} α n)
        (h : p.renameCells τ = q') (τ' : Fin p.card ≃ Fin q'.card)
        (hτ : ∀ i, (τ' i : ℕ) = τ.symm i) : q'.renameCells τ' = p := by
      subst h
      obtain rfl : τ' = τ.symm := Equiv.ext fun i ↦ Fin.ext (hτ i)
      rw [renameCells_renameCells, Equiv.symm_trans_self, renameCells_refl]
    exact key r.toEquiv q r.renameCells_eq _ fun _ ↦ rfl

/-- The composite of two renamings.  Native construction. -/
def trans (r : p.Renaming q) (r' : q.Renaming s) : p.Renaming s where
  toEquiv := r'.toEquiv.trans r.toEquiv
  renameCells_eq := by
    have key {k : ℕ} (τ : Fin k ≃ Fin p.card) (q' : StageType.{u} α n)
        (h : p.renameCells τ = q') (τ' : Fin s.card ≃ Fin q'.card)
        (h' : q'.renameCells τ' = s) (ρ : Fin s.card ≃ Fin p.card)
        (hρ : ∀ i (j : Fin k), (j : ℕ) = τ' i → ρ i = τ j) : p.renameCells ρ = s := by
      subst h
      obtain rfl : ρ = τ'.trans τ := Equiv.ext fun i ↦ hρ i (τ' i) rfl
      exact h'
    exact key r.toEquiv q r.renameCells_eq r'.toEquiv r'.renameCells_eq _ fun i j hj ↦ by
      rw [Fin.ext hj]
      rfl

@[simp] theorem refl_toEquiv (p : StageType.{u} α n) : (refl p).toEquiv = Equiv.refl _ := rfl

@[simp] theorem symm_toEquiv (r : p.Renaming q) : r.symm.toEquiv = r.toEquiv.symm := rfl

@[simp] theorem trans_toEquiv (r : p.Renaming q) (r' : q.Renaming s) :
    (r.trans r').toEquiv = r'.toEquiv.trans r.toEquiv :=
  rfl

/-- **A renaming reduces along stage reduction**, with the same bijection: stage reduction keeps
the cells and commutes with renaming (`StageType.reduce_renameCells`).  Native construction. -/
def reduce (r : p.Renaming q) (hβ : Order.IsSuccPrelimit β) :
    (p.reduce hβ).Renaming (q.reduce hβ) where
  toEquiv := r.toEquiv
  renameCells_eq := congrArg (StageType.reduce · hβ) r.renameCells_eq

@[simp] theorem reduce_toEquiv (r : p.Renaming q) (hβ : Order.IsSuccPrelimit β) :
    (r.reduce hβ).toEquiv = r.toEquiv :=
  rfl

/-- A renaming transported along equalities of its two stage types.  Native construction. -/
def copy {p' q' : StageType.{u} α n} (r : p.Renaming q) (hp : p = p') (hq : q = q') :
    p'.Renaming q' :=
  hp ▸ hq ▸ r

/-- The bijection of a transported renaming agrees with the original at equal positions.
Native construction. -/
theorem val_copy_toEquiv {p' q' : StageType.{u} α n} (r : p.Renaming q) (hp : p = p')
    (hq : q = q') {i : Fin q'.card} {i₀ : Fin q.card} (hi : (i : ℕ) = i₀) :
    ((r.copy hp hq).toEquiv i : ℕ) = r.toEquiv i₀ := by
  subst hp hq
  rw [Fin.ext hi]
  rfl

end Renaming

end StageType

/-! ### Coherent renaming -/

namespace Realization

open StageType

variable {α β : Ordinal.{u}} {M : Type v}

/-- **A coherent renaming** of `R` into `R'` (native construction), for two realizations at the
same stage on the same carrier:

* `isSome_eval_iff`: the same tuples are typed;
* `renamingAt`: at every tuple typed by `p` in `R` and by `q` in `R'`, a renaming of cells
  [AFK26, Definition 4.6] with `p = q.renameCells σ`, where `σ : Fin p.card ≃ Fin q.card`
  (`CoherentRenaming.cellEquiv`) sends each cell of `p` to the cell of `q` with the same scope,
  grade, label and row;
* `faceCellMap_comm`: the bijections commute with every face cell map: for `f : Fin m ↪ Fin n` and
  a tuple `t`, if `t` is typed by `p`, `q` and `f.trans t` by `p₀`, `q₀`, and the faces of `p`, `q`
  along `f` are `p₀`, `q₀`, then `faceCellMap hq ∘ σ (f.trans t) = σ t ∘ faceCellMap hp`.

For exactly consistent realizations the face equations hold whenever `f.trans t` is typed. -/
structure CoherentRenaming (R R' : Realization.{u, v} α M) where
  /-- The same tuples are typed. -/
  isSome_eval_iff : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), (R.eval t).isSome ↔ (R'.eval t).isSome
  /-- At a tuple typed in both, the type in `R` is a renaming of the type in `R'`. -/
  renamingAt : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) ⦃p q : StageType.{u} α n⦄, R.eval t = some p →
    R'.eval t = some q → q.Renaming p
  /-- The bijections of cells commute with the face cell maps. -/
  faceCellMap_comm : ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (f : Fin m ↪ Fin n)
    ⦃p q : StageType.{u} α n⦄ ⦃p₀ q₀ : StageType.{u} α m⦄ (hp : R.eval t = some p)
    (hq : R'.eval t = some q) (hp₀ : R.eval (f.trans t) = some p₀)
    (hq₀ : R'.eval (f.trans t) = some q₀) (hfp : restrictFace f p = some p₀)
    (hfq : restrictFace f q = some q₀) (i : Fin p₀.card),
    faceCellMap hfq ((renamingAt (f.trans t) hp₀ hq₀).toEquiv i) =
      (renamingAt t hp hq).toEquiv (faceCellMap hfp i)

/-- Two realizations **are coherent renamings** of each other when there is a coherent renaming.
Native construction. -/
def IsCoherentRenaming (R R' : Realization.{u, v} α M) : Prop :=
  Nonempty (CoherentRenaming R R')

namespace CoherentRenaming

variable {R R' R'' : Realization.{u, v} α M} {n : ℕ} {t : Fin n ↪ M} {p q : StageType.{u} α n}

/-- **The bijection of cells** of a coherent renaming at a tuple typed by `p` in `R` and by `q` in
`R'`: each cell of `p` goes to the cell of `q` with the same data.  Native construction. -/
def cellEquiv (c : CoherentRenaming R R') (t : Fin n ↪ M) (hp : R.eval t = some p)
    (hq : R'.eval t = some q) : Fin p.card ≃ Fin q.card :=
  (c.renamingAt t hp hq).toEquiv

/-- **Commutation with every face cell map**, in terms of `cellEquiv`.  Native construction. -/
theorem faceCellMap_cellEquiv (c : CoherentRenaming R R') {m : ℕ} (f : Fin m ↪ Fin n)
    {p₀ q₀ : StageType.{u} α m} (hp : R.eval t = some p) (hq : R'.eval t = some q)
    (hp₀ : R.eval (f.trans t) = some p₀) (hq₀ : R'.eval (f.trans t) = some q₀)
    (hfp : restrictFace f p = some p₀) (hfq : restrictFace f q = some q₀) (i : Fin p₀.card) :
    faceCellMap hfq (c.cellEquiv (f.trans t) hp₀ hq₀ i) = c.cellEquiv t hp hq (faceCellMap hfp i) :=
  c.faceCellMap_comm t f hp hq hp₀ hq₀ hfp hfq i

/-- **Commutation at every typed face, for exactly consistent realizations**: the face equations
are those given by consistency.  Native construction. -/
theorem faceCellMap_cellEquiv_of_isConsistent (c : CoherentRenaming R R') (hR : R.IsConsistent)
    (hR' : R'.IsConsistent) {m : ℕ} (f : Fin m ↪ Fin n) {p₀ q₀ : StageType.{u} α m}
    (hp : R.eval t = some p) (hq : R'.eval t = some q) (hp₀ : R.eval (f.trans t) = some p₀)
    (hq₀ : R'.eval (f.trans t) = some q₀) (i : Fin p₀.card) :
    faceCellMap ((hR' t q f hq).symm.trans hq₀) (c.cellEquiv (f.trans t) hp₀ hq₀ i) =
      c.cellEquiv t hp hq (faceCellMap ((hR t p f hp).symm.trans hp₀) i) :=
  c.faceCellMap_cellEquiv f hp hq hp₀ hq₀ _ _ i

/-! #### Preservation of the data of each cell -/

/-- The two types have the same plan.  Native construction. -/
theorem faces_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q) :
    p.toCellScheme.faces = q.toCellScheme.faces :=
  (c.renamingAt t hp hq).faces_eq

/-- The two types have the same number of cells.  Native construction. -/
theorem card_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q) :
    p.card = q.card := by
  simpa using Fintype.card_congr (c.cellEquiv t hp hq)

/-- **Labels are preserved.**  Native construction. -/
theorem label_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q)
    (i : Fin p.card) : p.label i = q.label (c.cellEquiv t hp hq i) :=
  (c.renamingAt t hp hq).label_eq i

/-- **Scopes are preserved.**  Native construction. -/
theorem scope_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q)
    (i : Fin p.card) :
    p.toCellScheme.scope i = q.toCellScheme.scope (c.cellEquiv t hp hq i) :=
  (c.renamingAt t hp hq).scope_eq i

/-- **Grades are preserved.**  Native construction. -/
theorem grade_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q)
    (i : Fin p.card) :
    p.toCellScheme.grade i = q.toCellScheme.grade (c.cellEquiv t hp hq i) :=
  (c.renamingAt t hp hq).grade_eq i

/-- **Graded indices are preserved.**  Native construction. -/
theorem gradedIndex_eq (c : CoherentRenaming R R') (hp : R.eval t = some p)
    (hq : R'.eval t = some q) (i : Fin p.card) :
    p.toCellScheme.gradedIndex i = q.toCellScheme.gradedIndex (c.cellEquiv t hp hq i) :=
  (c.renamingAt t hp hq).gradedIndex_eq i

/-- **Rows are preserved**, read through the bijection: the row of `i` at a cell `e` below it is
the row of `σ i` at `σ e`.  Native construction. -/
theorem row_eq (c : CoherentRenaming R R') (hp : R.eval t = some p) (hq : R'.eval t = some q)
    (i : Fin p.card) (e : p.toCellScheme.below (p.toCellScheme.gradedIndex i))
    (e' : q.toCellScheme.below (q.toCellScheme.gradedIndex (c.cellEquiv t hp hq i)))
    (he : e'.1 = c.cellEquiv t hp hq e.1) :
    p.rows.row i e = q.rows.row (c.cellEquiv t hp hq i) e' :=
  (c.renamingAt t hp hq).row_eq i e e' he

/-- The renaming at a tuple does not depend on the proofs of evaluation: at equal positions the
bijections agree.  Native construction. -/
theorem val_cellEquiv_congr (c : CoherentRenaming R R') {p' q' : StageType.{u} α n}
    (hp : R.eval t = some p) (hq : R'.eval t = some q) (hp' : R.eval t = some p')
    (hq' : R'.eval t = some q') {i : Fin p.card} {i' : Fin p'.card} (hi : (i : ℕ) = i') :
    (c.cellEquiv t hp hq i : ℕ) = c.cellEquiv t hp' hq' i' := by
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  rw [Fin.ext hi]

/-! #### Tuplewise renaming and class readings -/

/-- **A coherent renaming is a tuplewise renaming** (`Realization.IsCellRenamingOf`).  The
converse is not claimed: the tuplewise relation asks no compatibility of the bijections along
faces.  Native construction. -/
theorem isCellRenamingOf (c : CoherentRenaming R R') : R.IsCellRenamingOf R' := by
  intro n t
  cases hp : R.eval t with
  | none =>
    cases hq : R'.eval t with
    | none => exact Option.Rel.none
    | some q => exact absurd ((c.isSome_eval_iff t).mpr (by simp [hq])) (by simp [hp])
  | some p =>
    cases hq : R'.eval t with
    | none => exact absurd ((c.isSome_eval_iff t).mp (by simp [hp])) (by simp [hq])
    | some q =>
      have r := c.renamingAt t hp hq
      exact Option.Rel.some (IsCellRenaming.symm ⟨_, r.toEquiv, r.renameCells_eq⟩)

/-! #### Reflexivity, symmetry, transitivity -/

variable (R) in
/-- **Reflexivity**: the identity bijections form a coherent renaming of a realization into itself.
Native construction. -/
def refl : CoherentRenaming R R where
  isSome_eval_iff _ _ := Iff.rfl
  renamingAt _ _ _ _ hp hq := (Renaming.refl _).copy rfl (Option.some.inj (hp.symm.trans hq)).symm
  faceCellMap_comm _ _ _ _ p q p₀ q₀ hp hq hp₀ hq₀ hfp hfq i := by
    obtain rfl : p = q := Option.some.inj (hp.symm.trans hq)
    obtain rfl : p₀ = q₀ := Option.some.inj (hp₀.symm.trans hq₀)
    rfl

/-- **Symmetry**: the inverse bijections form a coherent renaming.  Native construction. -/
def symm (c : CoherentRenaming R R') : CoherentRenaming R' R where
  isSome_eval_iff _ t := (c.isSome_eval_iff t).symm
  renamingAt _ t _ _ hq hp := (c.renamingAt t hp hq).symm
  faceCellMap_comm _ _ t f q p q₀ p₀ hq hp hq₀ hp₀ hfq hfp i := by
    change faceCellMap hfp ((c.cellEquiv (f.trans t) hp₀ hq₀).symm i) =
      (c.cellEquiv t hp hq).symm (faceCellMap hfq i)
    rw [Equiv.eq_symm_apply, ← c.faceCellMap_cellEquiv f hp hq hp₀ hq₀ hfp hfq,
      Equiv.apply_symm_apply]

/-- The middle type of a composite: the type of `t` in `R'` when it is typed in `R`. -/
private theorem eval_some_get (c : CoherentRenaming R R') (hp : R.eval t = some p) :
    R'.eval t = some ((R'.eval t).get ((c.isSome_eval_iff t).mp (by simp [hp]))) :=
  (Option.some_get _).symm

/-- **Transitivity** through an exactly consistent middle realization: the composite bijections
form a coherent renaming.  Native construction. -/
def trans (c : CoherentRenaming R R') (c' : CoherentRenaming R' R'') (hR' : R'.IsConsistent) :
    CoherentRenaming R R'' where
  isSome_eval_iff _ t := (c.isSome_eval_iff t).trans (c'.isSome_eval_iff t)
  renamingAt _ t _ _ hp hs := (c'.renamingAt t (c.eval_some_get hp) hs).trans
    (c.renamingAt t hp (c.eval_some_get hp))
  faceCellMap_comm _ _ t f p s p₀ s₀ hp hs hp₀ hs₀ hfp hfs i := by
    have hfq : restrictFace f ((R'.eval t).get ((c.isSome_eval_iff t).mp (by simp [hp]))) =
        some ((R'.eval (f.trans t)).get ((c.isSome_eval_iff _).mp (by simp [hp₀]))) :=
      (hR' t _ f (c.eval_some_get hp)).symm.trans (c.eval_some_get hp₀)
    change faceCellMap hfs (c'.cellEquiv _ _ hs₀ (c.cellEquiv _ hp₀ _ i)) =
      c'.cellEquiv t _ hs (c.cellEquiv t hp _ (faceCellMap hfp i))
    rw [c'.faceCellMap_cellEquiv f _ hs _ hs₀ hfq hfs,
      c.faceCellMap_cellEquiv f hp _ hp₀ _ hfp hfq]

/-! #### Stage reduction -/

/-- The type of a tuple in the reduction is the reduction of its type.  Native construction. -/
theorem _root_.VaughtConjecture.Realization.reduce_eval_of_eval_eq_some
    (hβ : Order.IsSuccPrelimit β) (hp : R.eval t = some p) :
    (R.reduce hβ).eval t = some (p.reduce hβ) := by
  rw [reduce_eval, hp, Option.map_some]

/-- The type of `t` in `R` when it is typed in the reduction. -/
private theorem isSome_of_reduce {hβ : Order.IsSuccPrelimit β} {p' : StageType.{u} β n}
    (h : (R.reduce hβ).eval t = some p') : (R.eval t).isSome := by
  rw [← isSome_reduce_eval R hβ t, h]
  rfl

/-- The type in the reduction is the reduction of the type. -/
private theorem reduce_get {hβ : Order.IsSuccPrelimit β} {p' : StageType.{u} β n}
    (h : (R.reduce hβ).eval t = some p') :
    ((R.eval t).get (isSome_of_reduce h)).reduce hβ = p' := by
  rw [reduce_eval, ← Option.some_get (isSome_of_reduce h), Option.map_some] at h
  exact Option.some.inj h

/-- **A coherent renaming reduces along stage reduction** to a coherent renaming of the reductions,
with the same bijections (`CoherentRenaming.cellEquiv_reduce`), for exactly consistent
realizations: stage reduction keeps the cells and the faces.  Native construction. -/
def reduce (c : CoherentRenaming R R') (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hβ : Order.IsSuccPrelimit β) : CoherentRenaming (R.reduce hβ) (R'.reduce hβ) where
  isSome_eval_iff _ t := by
    rw [isSome_reduce_eval, isSome_reduce_eval]
    exact c.isSome_eval_iff t
  renamingAt _ t _ _ hp hq :=
    ((c.renamingAt t (Option.some_get (isSome_of_reduce hp)).symm
      (Option.some_get (isSome_of_reduce hq)).symm).reduce hβ).copy (reduce_get hq)
      (reduce_get hp)
  faceCellMap_comm _ _ t f p q p₀ q₀ hp hq hp₀ hq₀ hfp hfq i := by
    have hP : R.eval t = some ((R.eval t).get (isSome_of_reduce hp)) := (Option.some_get _).symm
    have hQ : R'.eval t = some ((R'.eval t).get (isSome_of_reduce hq)) :=
      (Option.some_get _).symm
    have hP₀ : R.eval (f.trans t) = some ((R.eval (f.trans t)).get (isSome_of_reduce hp₀)) :=
      (Option.some_get _).symm
    have hQ₀ : R'.eval (f.trans t) = some ((R'.eval (f.trans t)).get (isSome_of_reduce hq₀)) :=
      (Option.some_get _).symm
    have hfP := (hR t _ f hP).symm.trans hP₀
    have hfQ := (hR' t _ f hQ).symm.trans hQ₀
    have hc : ((R.eval (f.trans t)).get (isSome_of_reduce hp₀)).card = p₀.card :=
      congrArg (fun x : StageType.{u} β _ ↦ x.card) (reduce_get hp₀)
    have key := congrArg Fin.val
      (c.faceCellMap_cellEquiv f hP hQ hP₀ hQ₀ hfP hfQ (Fin.cast hc.symm i))
    have h₀ := Renaming.val_copy_toEquiv
      ((c.renamingAt (f.trans t) hP₀ hQ₀).reduce hβ) (reduce_get hq₀) (reduce_get hp₀)
      (i := i) (i₀ := Fin.cast hc.symm i) rfl
    have hs : q.toScheme = ((R'.eval t).get (isSome_of_reduce hq)).toScheme :=
      (congrArg (fun x : StageType.{u} β _ ↦ x.toScheme) (reduce_get hq)).symm
    refine Fin.ext ((val_faceCellMap_congr hfq hfQ hs h₀).trans (key.trans ?_))
    refine (Renaming.val_copy_toEquiv ((c.renamingAt t hP hQ).reduce hβ) (reduce_get hq)
      (reduce_get hp) ?_).symm
    exact val_faceCellMap_congr hfp hfP
      (congrArg (fun x : StageType.{u} β _ ↦ x.toScheme) (reduce_get hp)).symm rfl

/-- **The reduced coherent renaming has the same bijections.**  Native construction. -/
theorem cellEquiv_reduce (c : CoherentRenaming R R') (hR : R.IsConsistent)
    (hR' : R'.IsConsistent) (hβ : Order.IsSuccPrelimit β) (hp : R.eval t = some p)
    (hq : R'.eval t = some q) (i : Fin p.card) :
    (c.reduce hR hR' hβ).cellEquiv t (reduce_eval_of_eval_eq_some hβ hp)
      (reduce_eval_of_eval_eq_some hβ hq) i = c.cellEquiv t hp hq i := by
  have hp' := reduce_eval_of_eval_eq_some hβ hp
  have hq' := reduce_eval_of_eval_eq_some hβ hq
  have h := Renaming.val_copy_toEquiv
    ((c.renamingAt t (Option.some_get (isSome_of_reduce hp')).symm
      (Option.some_get (isSome_of_reduce hq')).symm).reduce hβ) (reduce_get hq') (reduce_get hp')
    (i := i) (i₀ := Fin.cast (congrArg (fun x : StageType.{u} α n ↦ x.card)
      (Option.some.inj ((Option.some_get _).trans hp))).symm i) rfl
  exact Fin.ext (h.trans (c.val_cellEquiv_congr _ _ hp hq rfl))

end CoherentRenaming

/-! ### Coherent renaming as a relation -/

namespace IsCoherentRenaming

variable {R R' R'' : Realization.{u, v} α M}

/-- Coherent renaming is reflexive.  Native construction. -/
theorem refl (R : Realization.{u, v} α M) : IsCoherentRenaming R R :=
  ⟨CoherentRenaming.refl R⟩

/-- Coherent renaming is symmetric.  Native construction. -/
theorem symm (h : IsCoherentRenaming R R') : IsCoherentRenaming R' R :=
  let ⟨c⟩ := h
  ⟨c.symm⟩

/-- Coherent renaming is transitive through an exactly consistent middle realization.
Native construction. -/
theorem trans (h : IsCoherentRenaming R R') (h' : IsCoherentRenaming R' R'')
    (hR' : R'.IsConsistent) : IsCoherentRenaming R R'' :=
  let ⟨c⟩ := h
  let ⟨c'⟩ := h'
  ⟨c.trans c' hR'⟩

/-- Coherent renaming reduces along stage reduction, for exactly consistent realizations.
Native construction. -/
theorem reduce (h : IsCoherentRenaming R R') (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hβ : Order.IsSuccPrelimit β) : IsCoherentRenaming (R.reduce hβ) (R'.reduce hβ) :=
  let ⟨c⟩ := h
  ⟨c.reduce hR hR' hβ⟩

/-- Coherently renamed realizations have the same class reading.  Native construction. -/
theorem classReading_eq (h : IsCoherentRenaming R R') : R.classReading = R'.classReading :=
  let ⟨c⟩ := h
  R.classReading_eq_classReading_iff.mpr c.isCellRenamingOf

end IsCoherentRenaming

variable (α M) in
/-- **Coherent renaming is an equivalence relation on the exactly consistent realizations.**
Native construction. -/
theorem isCoherentRenaming_equivalence :
    Equivalence fun R R' : {R : Realization.{u, v} α M // R.IsConsistent} ↦
      IsCoherentRenaming R.1 R'.1 :=
  ⟨fun R ↦ .refl R.1, fun h ↦ h.symm, fun {_ R' _} h h' ↦ h.trans h' R'.2⟩

/-- **Coherently renamed realizations have the same class reading**: a coherent renaming is a
tuplewise renaming (`Realization.CoherentRenaming.isCellRenamingOf`), and tuplewise renamings
have the same class reading (`Realization.classReading_eq_classReading_iff`).  The converse is
not claimed.  Native construction. -/
theorem classReading_eq_of_coherentRenaming {R R' : Realization.{u, v} α M}
    (c : CoherentRenaming R R') : R.classReading = R'.classReading :=
  R.classReading_eq_classReading_iff.mpr c.isCellRenamingOf

end Realization

end

end VaughtConjecture

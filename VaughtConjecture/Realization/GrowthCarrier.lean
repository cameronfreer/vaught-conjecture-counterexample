/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Realization.Model

/-!
# Growth carriers and their recovery

Roadmap, Layer 3 (the growth carrier of (R3) and (R4)).  One finite object serves both growth
statements: a legal scheme `E` on the points of an actual private context and one new point, with
the context as its face along the first points and a donor as its face along a root followed by
the new point.  It is realized **once**, in the original model, by generalized saturation, and the
donor's labels are then **read from an evaluator** on the realized occurrence.  The evaluator may
be the actual labels (for (R3)) or the stable labels (for (R4)); it need not come from a model,
and its values need not lie below the stage.

## Main definitions

* `Realization.OccurrenceLabelling`: an **evaluator of actual occurrences** of a realization `R`: a
  labelling `label u t` of the cells of `t` at every tuple `u` of type `t`, lawful for the rows of
  `t` and compatible with restriction to closed faces.  Nothing else is asked: no saturation, no
  modelhood, no bound by the stage.
* `Realization.typeLabelling`: the labels of the types themselves.
* `GrowthCarrier C P e`: a legal scheme on `J + 1` points whose face along the first `J` points is
  the context scheme `C` and whose face along `extendByLast e` is the donor scheme `P`.
* `GrowthCarrier.Recovers σ ρ`: the **recovery** of the carrier: every lawful section of its rows
  that agrees with `σ` on the context face satisfies the relation `ρ` on the donor face.  The
  sections are arbitrary lawful sections, with no stage bound; this quantifier is what lets one
  carrier be evaluated by several labellings.

## Main statements

* `GrowthCarrier.mem_cofaces_displayType`, **legality of the carrier**: a lawful display of the
  carrier at the stage, agreeing with an actual context type on the context face, is a legal
  coface of that type on the carrier, so the instance of generalized saturation at the carrier is
  nonempty (`GrowthCarrier.nonempty_cofaces_inter_saturationFamily`).
* `GrowthCarrier.exists_recovered_of_eval`, **the evaluation**: at any tuple realizing the carrier
  over the context, the evaluator's labels at the donor face satisfy the recovered relation.
* `GrowthCarrier.exists_recovered`, **the recovery in a model** (the growth engine): realizing the
  carrier once by generalized saturation, some point extends the root, fresh over the context,
  to a tuple whose type is on the donor scheme and whose evaluated labels satisfy the relation.
* `GrowthCarrier.exists_eval_eq_of_recovers_eq`, **exact receiving from exact recovery**: with
  the actual labels and the relation `ℓ = D j`, the type of the received tuple is `D` itself,
  the formal top included.

The carrier's construction is not part of this file: it is an input.  No coding bound on rows
beyond the native law (`Scheme.IsCoded`, values below `ω ^ 2`) is used.

## References

Generalized saturation is [Kni26, Definition 3.2.1, clause 4(a)i]; restriction of stage types is
[Kni26, Definition 3.1.2]; the growth construction is that of [Kni26, §4] for the continuation of
a model at a limit stage.
-/

universe u v

namespace VaughtConjecture

open Finset StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {n m : ℕ}

/-! ### Evaluators of actual occurrences -/

/-- An **evaluator of the actual occurrences** of `R`: at every tuple `u` of type `t`, a
labelling of the cells of `t`, lawful for the rows of `t`, and literally compatible with the
restriction to every closed face.  No saturation, no modelhood, and no bound by the stage is
required: its values are arbitrary labels. -/
structure OccurrenceLabelling (R : Realization.{u, v} α M) where
  /-- The label of a cell of `t` at the tuple `u`. -/
  label {n : ℕ} : (Fin n ↪ M) → (t : StageType.{u} α n) → Fin t.card → Label.{u}
  /-- At a tuple of type `t`, the labelling is a lawful section of the rows of `t`. -/
  isLawful ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} α n) :
    R.eval u = some t → t.rows.IsLawful (label u t)
  /-- Restriction to a closed face reads the labels of the visible cells. -/
  label_comap ⦃n m : ℕ⦄ (w : Fin m ↪ M) (q : StageType.{u} α m) (f : Fin n ↪ Fin m)
    (hf : univ.map f ∈ q.toCellScheme.faces) (i : Fin (q.comap f hf).card) :
    R.eval w = some q → label (f.trans w) (q.comap f hf) i = label w q (q.cellMap f i)

variable {R : Realization.{u, v} α M}

/-- The labels of an evaluator agree at equal tuples, equal types and cells at equal positions. -/
theorem OccurrenceLabelling.label_congr (L : R.OccurrenceLabelling) {u u' : Fin n ↪ M} (hu : u = u')
    {t t' : StageType.{u} α n} (ht : t = t') {i : Fin t.card} {j : Fin t'.card}
    (hij : (i : ℕ) = j) : L.label u t i = L.label u' t' j := by
  subst hu ht
  rw [Fin.ext hij]

variable (R) in
/-- The **actual labels**: the labels of the types themselves. -/
def typeLabelling : R.OccurrenceLabelling where
  label _ t := t.label
  isLawful _ _ t _ := t.isLawful
  label_comap _ _ _ _ _ _ _ _ := rfl

@[simp] theorem typeLabelling_label (u : Fin n ↪ M) (t : StageType.{u} α n) :
    (typeLabelling R).label u t = t.label :=
  rfl

end Realization

/-! ### Growth carriers -/

/-- A **growth carrier** for the context scheme `C` on `J` points and the donor scheme `P` on
`n + 1` points attached along `e : Fin n ↪ Fin J`: a legal scheme on `J + 1` points whose face
along the first `J` points is `C` and whose face along `e` followed by the new point is `P`. -/
structure GrowthCarrier {J n : ℕ} (C : Scheme.{u} J) (P : Scheme.{u} (n + 1))
    (e : Fin n ↪ Fin J) where
  /-- The carrier scheme. -/
  scheme : Scheme.{u} (J + 1)
  /-- The carrier is legal. -/
  isLegal : scheme.IsLegal
  /-- The context face is closed. -/
  context_mem : univ.map Fin.castSuccEmb ∈ scheme.toCellScheme.faces
  /-- The context face is the context scheme. -/
  comap_context : scheme.comap Fin.castSuccEmb = C
  /-- The donor face is closed. -/
  donor_mem : univ.map (extendByLast e) ∈ scheme.toCellScheme.faces
  /-- The donor face is the donor scheme. -/
  comap_donor : scheme.comap (extendByLast e) = P

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {C : Scheme.{u} J} {P : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier C P e)

/-- The **recovery** of a growth carrier, from the context section `σ`, of the relation `ρ`: every
lawful section of the carrier's rows that is `σ` on the context face satisfies `ρ` at every cell of
the donor face.  The sections are arbitrary lawful sections: no stage bound. -/
def Recovers (σ : Fin C.card → Label.{u}) (ρ : Fin P.card → Label.{u} → Prop) : Prop :=
  ∀ v : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful v →
    (∀ (i : Fin (G.scheme.comap Fin.castSuccEmb).card) (j : Fin C.card), (i : ℕ) = j →
      v (G.scheme.cellMap Fin.castSuccEmb i) = σ j) →
    ∀ (i : Fin (G.scheme.comap (extendByLast e)).card) (j : Fin P.card), (i : ℕ) = j →
      ρ j (v (G.scheme.cellMap (extendByLast e) i))

/-- Recovery of a relation gives recovery of every weaker relation. -/
theorem Recovers.mono {σ : Fin C.card → Label.{u}} {ρ ρ' : Fin P.card → Label.{u} → Prop}
    (h : G.Recovers σ ρ) (hρ : ∀ j ℓ, ρ j ℓ → ρ' j ℓ) : G.Recovers σ ρ' :=
  fun v hv hc i j hij ↦ hρ j _ (h v hv hc i j hij)

/-! ### Legality of the carrier -/

/-- The **display type** of a growth carrier: the stage type at `α` on the carrier scheme with a
lawful display `w` at the stage. -/
def displayType (w : Fin G.scheme.card → Label.{u}) (hw : G.scheme.rows.IsLawful w)
    (hst : ∀ d, Label.AtStage α (w d)) : StageType.{u} α (J + 1) where
  toScheme := G.scheme
  label := w
  isWellFormed := G.isLegal.isWellFormed
  isCoded := G.isLegal.isCoded
  isLawful := hw
  atStage := hst

/-- **Legality of the carrier**: a lawful display of the carrier at the stage that agrees, on the
context face, with a stage type `t` on the context scheme is a legal coface of `t`. -/
theorem mem_cofaces_displayType {w : Fin G.scheme.card → Label.{u}}
    (hw : G.scheme.rows.IsLawful w) (hst : ∀ d, Label.AtStage α (w d))
    {t : StageType.{u} α J} (ht : t.toScheme = C)
    (hctx : ∀ (i : Fin (G.scheme.comap Fin.castSuccEmb).card) (j : Fin t.card), (i : ℕ) = j →
      w (G.scheme.cellMap Fin.castSuccEmb i) = t.label j) :
    G.displayType w hw hst ∈ t.cofaces := by
  refine ⟨G.isLegal, (restrictFace_of_mem _ _ G.context_mem).trans (congrArg some ?_)⟩
  exact StageType.ext (G.comap_context.trans ht.symm) hctx

/-- A lawful display of the carrier gives a nonempty instance of generalized saturation at the
carrier over every stage type it displays on the context face. -/
theorem nonempty_cofaces_inter_saturationFamily {w : Fin G.scheme.card → Label.{u}}
    (hw : G.scheme.rows.IsLawful w) (hst : ∀ d, Label.AtStage α (w d))
    {t : StageType.{u} α J} (ht : t.toScheme = C)
    (hctx : ∀ (i : Fin (G.scheme.comap Fin.castSuccEmb).card) (j : Fin t.card), (i : ℕ) = j →
      w (G.scheme.cellMap Fin.castSuccEmb i) = t.label j) :
    (t.cofaces ∩ saturationFamily G.scheme).Nonempty :=
  ⟨_, G.mem_cofaces_displayType hw hst ht hctx, rfl⟩

/-! ### The evaluation on a realized carrier -/

variable {M : Type v} {R : Realization.{u, v} α M}

/-- **The evaluation on a realized carrier**: let `w` realize the carrier over an occurrence `x`
(its first points are `x`, its type `r` is on the carrier scheme).  If the carrier recovers `ρ`
from the evaluator's labels of `x`, then the face of `w` along `e` followed by the new point has
a type on the donor scheme at which the evaluator's labels satisfy `ρ`.  Only exact consistency
of `R` is used. -/
theorem exists_recovered_of_eval (hR : R.IsConsistent) (L : R.OccurrenceLabelling)
    {x : R.Occurrence} {e : Fin n ↪ Fin x.arity} (G : GrowthCarrier x.type.toScheme P e)
    {ρ : Fin P.card → Label.{u} → Prop} (hrec : G.Recovers (L.label x.tuple x.type) ρ)
    {w : Fin (x.arity + 1) ↪ M} (hw : Fin.castSuccEmb.trans w = x.tuple)
    {r : StageType.{u} α (x.arity + 1)} (hr : R.eval w = some r) (hrE : r.toScheme = G.scheme) :
    ∃ s : StageType.{u} α (n + 1), R.eval ((extendByLast e).trans w) = some s ∧
      s.toScheme = P ∧ ∀ (i : Fin s.card) (j : Fin P.card), (i : ℕ) = j →
        ρ j (L.label ((extendByLast e).trans w) s i) := by
  obtain ⟨S, lab, hwf, hcod, hlaw, hst⟩ := r
  change S = G.scheme at hrE
  subst hrE
  set r : StageType.{u} α (x.arity + 1) := ⟨G.scheme, lab, hwf, hcod, hlaw, hst⟩
  have hc : univ.map Fin.castSuccEmb ∈ r.toCellScheme.faces := G.context_mem
  have hd : univ.map (extendByLast e) ∈ r.toCellScheme.faces := G.donor_mem
  have hctx : r.comap Fin.castSuccEmb hc = x.type := by
    have h := (hR w r _ hr).symm.trans (hw ▸ x.eval_tuple)
    rw [restrictFace_of_mem r _ hc] at h
    exact Option.some_injective _ h
  refine ⟨r.comap (extendByLast e) hd, (hR w r _ hr).trans (restrictFace_of_mem r _ hd),
    G.comap_donor, fun i j hij ↦ ?_⟩
  rw [L.label_comap w r _ hd i hr]
  refine hrec (L.label w r) (L.isLawful w r hr) (fun i' j' hij' ↦ ?_) i j hij
  rw [← L.label_comap w r _ hc i' hr]
  exact L.label_congr hw hctx hij'

/-- The new point of a tuple realizing the carrier over `x` is off the tuple of `x`. -/
theorem last_notMem_range {x : R.Occurrence} {e : Fin n ↪ Fin x.arity} {w : Fin (x.arity + 1) ↪ M}
    (hw : Fin.castSuccEmb.trans w = x.tuple) :
    ((extendByLast e).trans w) (Fin.last n) ∉ Set.range x.tuple := by
  rintro ⟨i, hi⟩
  rw [← hw, Function.Embedding.trans_apply, Function.Embedding.trans_apply,
    extendByLast_last] at hi
  exact (Fin.castSucc_lt_last i).ne (w.injective hi)

/-- The face of a tuple realizing the carrier along `e` followed by the new point keeps the root:
its first points are the root `e` of `x`. -/
theorem castSuccEmb_trans_extendByLast_trans {x : R.Occurrence} {e : Fin n ↪ Fin x.arity}
    {w : Fin (x.arity + 1) ↪ M} (hw : Fin.castSuccEmb.trans w = x.tuple) :
    Fin.castSuccEmb.trans ((extendByLast e).trans w) = e.trans x.tuple := by
  rw [← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
    Function.Embedding.trans_assoc, hw]

/-! ### The growth engine -/

/-- **The growth engine**: in a model, if a growth carrier over an occurrence `x` has a nonempty
instance of generalized saturation over `x` (`nonempty_cofaces_inter_saturationFamily`) and
recovers `ρ` from the evaluator's labels of `x`, then some point, fresh over `x`, extends the root
`e` of `x` to a tuple whose type is on the donor scheme and at which the evaluator's labels satisfy
`ρ`.  The carrier is realized once, in `R`; the relation is read from the evaluator on the
realized tuple.  The evaluator need not be the labels of a model. -/
theorem exists_recovered (hR : R.IsModel) (L : R.OccurrenceLabelling) (x : R.Occurrence)
    {e : Fin n ↪ Fin x.arity} (G : GrowthCarrier x.type.toScheme P e)
    (hsat : (x.type.cofaces ∩ saturationFamily G.scheme).Nonempty)
    {ρ : Fin P.card → Label.{u} → Prop} (hrec : G.Recovers (L.label x.tuple x.type) ρ) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = e.trans x.tuple ∧
      u (Fin.last n) ∉ Set.range x.tuple ∧ ∃ s : StageType.{u} α (n + 1), R.eval u = some s ∧
        s.toScheme = P ∧ ∀ (i : Fin s.card) (j : Fin P.card), (i : ℕ) = j →
          ρ j (L.label u s i) := by
  obtain ⟨w, hw, r, hrE, hr⟩ := hR.saturation x G.scheme hsat
  exact ⟨_, castSuccEmb_trans_extendByLast_trans hw, last_notMem_range hw,
    G.exists_recovered_of_eval hR.isConsistent L hrec hw hr hrE⟩

/-- **Exact receiving from exact recovery**: if a growth carrier over `x`, with a nonempty
saturation instance, recovers the labels of a stage type `D` exactly from the actual labels of
`x`, then some point, fresh over `x`, extends the root `e` of `x` to a tuple of type `D`, the
formal top included. -/
theorem exists_eval_eq_of_recovers_eq (hR : R.IsModel) (x : R.Occurrence)
    {e : Fin n ↪ Fin x.arity} {D : StageType.{u} α (n + 1)}
    (G : GrowthCarrier x.type.toScheme D.toScheme e)
    (hsat : (x.type.cofaces ∩ saturationFamily G.scheme).Nonempty)
    (hrec : G.Recovers x.type.label fun j ℓ ↦ ℓ = D.label j) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = e.trans x.tuple ∧
      u (Fin.last n) ∉ Set.range x.tuple ∧ R.eval u = some D := by
  obtain ⟨u, hu, hnew, s, hs, hsD, hl⟩ :=
    G.exists_recovered hR (Realization.typeLabelling R) x hsat hrec
  exact ⟨u, hu, hnew, hs.trans (congrArg some (StageType.ext hsD hl))⟩

end GrowthCarrier

end VaughtConjecture

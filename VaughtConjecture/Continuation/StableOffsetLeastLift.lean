/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Stage.LeastLift

/-!
# The stable offset as a supremum of least-lift offsets

Roadmap, Layer 3, 3.1, derived statement (b), the threshold characterization, in its supremum
form; Layer 4, output 2 (the stable values on rooted covers).

Let `S` be a realization at a stage `β` that is zero or a limit, `c` a tuple, `p` a stage type at
`β` on the arity of `c` (the root) and `d` a cell of `p`.  The stable offset of `d` at `c` in `S`
(`Realization.stableOffset`, in `VaughtConjecture.Continuation.Normalization`) is the supremum,
over the **rooted covers** `x = (m, q, f)` of `c` in `S` (`Realization.ExtendsToCover`), of the
provisional offsets `StageType.provisionalOffset α hβ q f p d`.  This file reads the same supremum,
over the same index family, through least lift labellings
(`StageType.IsLiftLabelling`, `VaughtConjecture.Stage.LeastLift`).

**The offset of a labelling at the transported cell** (`StageType.labellingOffset`).  For a
labelling `ℓ` of the cells of `q`, it is the supremum in `ℕ∞` of the `n` such that `q` restricts to
`p` along `f` and `β + n ≤ ℓ e` at the cell `e` of `q` transported from `d`, that is,
`q.cellMap f i = e` for the cell `i` of the face at the position of `d`.  The restriction of `q` to
the root and the literal cell transport are part of the definition, exactly as in
`StageType.forcesThreshold_iff_coe_add_le_of_isLeast`; a cover not restricting to `p` along `f`
has offset `0`, as it has provisional offset `0` (it forces nothing).

**Results.**

* **Per cover** (`StageType.provisionalOffset_eq_labellingOffset`): for `β` zero or a limit and
  any least lift labelling `ℓ₀` of `q` to `α`, the provisional offset of `d` at `(q, f)` is the
  offset of `ℓ₀` at the transported cell.  No other premise: no legality, no bound on `α`, no
  hypothesis on the label of `d`, and no restriction of `q` to `p` assumed (it is read inside).
* **Supremum form, for any least-lift family**
  (`Realization.stableOffset_eq_iSup_labellingOffset`): if `ℓ₀ x` is a least lift labelling of
  the type of `x` for every rooted cover `x` of `c` in `S`, the stable offset is the supremum, over
  the rooted covers of `c` in `S`, of the offsets of the `ℓ₀ x` at the transported cell.  The
  index family is that of `Realization.stableOffset`, unchanged.  The threshold forms
  (`Realization.natCast_le_stableOffset_iff_exists_isLeast`,
  `Realization.coe_add_le_stableLabel_iff_exists_isLeast`) add the premises of
  `Realization.natCast_le_stableOffset_iff`, that `c` covers `p` in `S` and `d` is labelled `⊤`
  in `p`: then `n` is at most the stable offset exactly when some rooted cover `(m, q, f)` of `c`
  in `S` has `q` restricting to `p` along `f` and `β + n ≤ ℓ₀ x e` at the transported cell `e`.
  These premises enter only at `n = 0`, where the root itself, `(k, p, id)`, is a rooted cover
  forcing `0` (as in `Realization.natCast_le_stableOffset_iff`); the equality form needs neither.
  These forms take the family `ℓ₀` as a hypothesis; its existence is a separate statement, below.
* **Legality of the cover types** (`Realization.ExtendsToCover.isLegal`).  The definition of the
  stable offset and its forcing form `Realization.natCast_le_stableOffset_iff` place no condition
  on the types of `S`: `S` is any realization at `β`, and these hypotheses do not include
  legality of the type of a rooted cover.  It is taken here from one additional, named premise,
  `S.HasLegalTypes`: with it, every rooted cover has a legal type.
* **Existence of the least lifts** (`Realization.exists_isLeast_isLiftLabelling_family`): given
  `S.HasLegalTypes`, `β` a limit and `β + ω ≤ α`, some family `ℓ₀` is a least lift labelling at
  every rooted cover.  These three premises are sufficient for the existence, through
  `StageType.exists_isLeast_isLiftLabelling`; they are not shown necessary or minimal.  The
  stable offset itself carries only `β` zero or a limit and any `α`.  Hence the supremum form and
  the threshold form with a least lift at each rooted cover
  (`Realization.exists_stableOffset_eq_iSup_labellingOffset`,
  `Realization.exists_natCast_le_stableOffset_iff_exists_isLeast`), and at consecutive block stages
  for the reduction of a realization with legal types
  (`Realization.exists_natCast_le_stableOffset_reduce_iff_exists_isLeast`).

A least lift labelling is unique when it exists (`IsLeast.unique`), so the choice of family does
not matter.  A stable offset `⊤` says that every `n` is reached at some rooted cover, the cover
depending on `n`; it does not say that one rooted cover has least-lift offset `⊤`.  No change is
made to `Realization.stableOffset` or to the statements of
`VaughtConjecture.Continuation.Normalization`.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Order
open scoped Ordinal

namespace StageType

variable {α β : Ordinal.{u}} {m k : ℕ} {q : StageType.{u} β m} {f : Fin k ↪ Fin m}
  {p : StageType.{u} β k} {d : Fin p.card}

/-- A stage type restricting to `p` along `f` has a cell transported from each cell `d` of `p`:
the cell `q.cellMap f i` for the cell `i` of the face at the position of `d`. -/
theorem exists_transported_cell (hfp : restrictFace f q = some p) (d : Fin p.card) :
    ∃ e : Fin q.card, ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hfp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β k ↦ s.card) hqp
  set i₀ : Fin (q.toScheme.comap f).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  exact ⟨q.cellMap f i₀, fun i hi ↦ congrArg (q.cellMap f) (Fin.ext hi)⟩

/-- **Forcing is read by any least lift, at the transported cell.**  Let `β` be zero or a limit
and `ℓ₀` a least lift labelling of `q` to `α`.  Then `(q, f)` forces `n` at `d` exactly when `q`
restricts to `p` along `f` and `β + n ≤ ℓ₀ e` at a cell `e` of `q` transported from `d`.  No other
premise is used. -/
theorem forcesThreshold_iff_exists_coe_add_le_of_isLeast (hβ : IsSuccPrelimit β)
    {ℓ₀ : Fin q.card → Label.{u}} (hleast : IsLeast {ℓ | q.IsLiftLabelling α ℓ} ℓ₀) {n : ℕ} :
    ForcesThreshold α hβ q f p d n ↔ restrictFace f q = some p ∧
      ∃ e : Fin q.card, (∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) ∧
        ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ e := by
  refine ⟨fun h ↦ ?_, fun ⟨hfp, e, he, hle⟩ ↦
    (forcesThreshold_iff_coe_add_le_of_isLeast hβ hfp he hleast).mpr hle⟩
  obtain ⟨e, he⟩ := exists_transported_cell h.1 d
  exact ⟨h.1, e, he, (forcesThreshold_iff_coe_add_le_of_isLeast hβ h.1 he hleast).mp h⟩

variable (β f p d) in
/-- The **offset of a labelling** `ℓ` of the cells of `q` at the cell transported from the cell
`d` of the root `p`: the supremum in `ℕ∞` of the `n` such that `q` restricts to `p` along `f` and
`β + n ≤ ℓ e` at a cell `e` of `q` transported from `d`. -/
noncomputable def labellingOffset (ℓ : Fin q.card → Label.{u}) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : restrictFace f q = some p ∧
      ∃ e : Fin q.card, (∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) ∧
        ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ e), (n : ℕ∞)

/-- **The provisional offset is the offset of any least lift.**  For `β` zero or a limit and a
least lift labelling `ℓ₀` of `q` to `α`, the provisional offset of `d` at `(q, f)` is the offset
of `ℓ₀` at the cell transported from `d`.  No other premise is used. -/
theorem provisionalOffset_eq_labellingOffset (hβ : IsSuccPrelimit β)
    {ℓ₀ : Fin q.card → Label.{u}} (hleast : IsLeast {ℓ | q.IsLiftLabelling α ℓ} ℓ₀) :
    provisionalOffset α hβ q f p d = labellingOffset β f p d ℓ₀ :=
  iSup_congr fun _ ↦ iSup_congr_Prop
    (forcesThreshold_iff_exists_coe_add_le_of_isLeast hβ hleast) fun _ ↦ rfl

end StageType

namespace Realization

variable {α β : Ordinal.{u}} {M : Type v} {k : ℕ} {S : Realization.{u, v} β M}
  {hβ : IsSuccPrelimit β} {c : Fin k → M} {p : StageType.{u} β k} {d : Fin p.card}

/-! ### Least lifts at the rooted covers -/

/-- **Rooted covers have legal types** in a realization with legal types: the type of a rooted
cover is the type of an actual tuple. -/
theorem ExtendsToCover.isLegal (hS : S.HasLegalTypes)
    {x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)} (hx : S.ExtendsToCover c x) :
    x.2.1.IsLegal := by
  obtain ⟨s, -, hs⟩ := hx
  exact hS _ _ hs.eval_eq

/-- **A least lift at every rooted cover**: for `S` with legal types, `β` a limit and
`β + ω ≤ α`, some family `ℓ₀` assigns to every rooted cover `x` of `c` in `S` a least lift
labelling of its type to `α`.  The three premises are sufficient, through
`StageType.exists_isLeast_isLiftLabelling` with legality from `S.HasLegalTypes`; they are not
shown necessary or minimal. -/
theorem exists_isLeast_isLiftLabelling_family (hS : S.HasLegalTypes) (hlim : IsSuccLimit β)
    (hα : β + ω ≤ α) (c : Fin k → M) :
    ∃ ℓ₀ : ∀ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), Fin x.2.1.card → Label.{u},
      ∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x) := by
  choose ℓ₀ hℓ₀ using fun x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m) ↦
    show ∃ ℓ₀ : Fin x.2.1.card → Label.{u},
        S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} ℓ₀ by
      by_cases hx : S.ExtendsToCover c x
      · obtain ⟨ℓ₀, h⟩ := StageType.exists_isLeast_isLiftLabelling hlim hα (hx.isLegal hS)
        exact ⟨ℓ₀, fun _ ↦ h⟩
      · exact ⟨x.2.1.label, fun h ↦ absurd h hx⟩
  exact ⟨ℓ₀, hℓ₀⟩

/-! ### The supremum form, for any least-lift family -/

section Family

variable (ℓ₀ : ∀ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), Fin x.2.1.card → Label.{u})

/-- **The stable offset is the supremum of the least-lift offsets.**  For `β` zero or a limit, if
`ℓ₀ x` is a least lift labelling to `α` of the type of every rooted cover `x` of `c` in `S`, the
stable offset of `d` at `c` is the supremum, over the rooted covers of `c` in `S` (the index
family of `Realization.stableOffset`), of the offset of `ℓ₀ x` at the cell transported from `d`
(`StageType.labellingOffset`, which reads the restriction of the cover's type to `p`). -/
theorem stableOffset_eq_iSup_labellingOffset
    (hleast : ∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x)) :
    S.stableOffset α hβ c p d = ⨆ (x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m))
      (_ : S.ExtendsToCover c x), StageType.labellingOffset β x.2.2 p d (ℓ₀ x) :=
  iSup_congr fun x ↦ iSup_congr fun hx ↦
    StageType.provisionalOffset_eq_labellingOffset hβ (hleast x hx)

/-- **The thresholds of the stable offset, read by least lifts.**  For `β` zero or a limit, `c`
covering the root `p` in `S`, `d` labelled `⊤` in `p`, and `ℓ₀ x` a least lift labelling to `α` of
the type of every rooted cover `x` of `c` in `S`: `n` is at most the stable offset exactly when
some rooted cover `(m, q, f)` of `c` in `S` has `q` restricting to `p` along `f` and
`β + n ≤ ℓ₀ x e` at a cell `e` of `q` transported from `d`. -/
theorem natCast_le_stableOffset_iff_exists_isLeast (hc : S.Covers p c) (hd : p.label d = ⊤)
    (hleast : ∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x))
    {n : ℕ} :
    (n : ℕ∞) ≤ S.stableOffset α hβ c p d ↔
      ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), S.ExtendsToCover c x ∧
        StageType.restrictFace x.2.2 x.2.1 = some p ∧ ∃ e : Fin x.2.1.card,
          (∀ i : Fin (x.2.1.toScheme.comap x.2.2).card, (i : ℕ) = d →
            x.2.1.cellMap x.2.2 i = e) ∧ ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ x e := by
  rw [natCast_le_stableOffset_iff hc hd]
  exact ⟨fun ⟨x, h, hx⟩ ↦ ⟨x, hx,
      (StageType.forcesThreshold_iff_exists_coe_add_le_of_isLeast hβ (hleast x hx)).mp h⟩,
    fun ⟨x, hx, h⟩ ↦ ⟨x,
      (StageType.forcesThreshold_iff_exists_coe_add_le_of_isLeast hβ (hleast x hx)).mpr h, hx⟩⟩

/-- **The thresholds of the stable label, read by least lifts**: under the hypotheses of
`Realization.natCast_le_stableOffset_iff_exists_isLeast`, the stable label is at least `β + n`
exactly when some rooted cover `(m, q, f)` of `c` in `S` has `q` restricting to `p` along `f` and
`β + n ≤ ℓ₀ x e` at a cell `e` of `q` transported from `d`. -/
theorem coe_add_le_stableLabel_iff_exists_isLeast (hc : S.Covers p c) (hd : p.label d = ⊤)
    (hleast : ∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x))
    {n : ℕ} :
    ((β + n : Ordinal.{u}) : Label.{u}) ≤ S.stableLabel α hβ c p d ↔
      ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), S.ExtendsToCover c x ∧
        StageType.restrictFace x.2.2 x.2.1 = some p ∧ ∃ e : Fin x.2.1.card,
          (∀ i : Fin (x.2.1.toScheme.comap x.2.2).card, (i : ℕ) = d →
            x.2.1.cellMap x.2.2 i = e) ∧ ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ x e :=
  Label.coe_add_le_ofOffset_iff.trans (natCast_le_stableOffset_iff_exists_isLeast ℓ₀ hc hd hleast)

end Family

/-! ### With legal types -/

/-- **The supremum form with a least lift at each rooted cover**, given legal types.  For `S`
with legal types (`S.HasLegalTypes`, giving the legality of the type of each rooted cover, which
the hypotheses of the stable offset do not include), `β` a limit and `β + ω ≤ α`, sufficient
premises for the existence of the least lifts (not shown necessary or minimal), some family `ℓ₀`
is a least lift labelling at every rooted cover of `c` in `S`, and the stable offset of `d` at `c`
is the supremum, over the rooted covers of `c` in `S`, of the offsets of the `ℓ₀ x` at the cell
transported from `d`. -/
theorem exists_stableOffset_eq_iSup_labellingOffset (hS : S.HasLegalTypes) (hlim : IsSuccLimit β)
    (hα : β + ω ≤ α) :
    ∃ ℓ₀ : ∀ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), Fin x.2.1.card → Label.{u},
      (∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x)) ∧
        S.stableOffset α hβ c p d = ⨆ (x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m))
          (_ : S.ExtendsToCover c x), StageType.labellingOffset β x.2.2 p d (ℓ₀ x) := by
  obtain ⟨ℓ₀, hleast⟩ := exists_isLeast_isLiftLabelling_family hS hlim hα c
  exact ⟨ℓ₀, hleast, stableOffset_eq_iSup_labellingOffset ℓ₀ hleast⟩

/-- **The thresholds of the stable offset with a least lift at each rooted cover**, given legal
types.  For `S` with legal types, `β` a limit and `β + ω ≤ α` (sufficient premises for the
existence of the least lifts, not shown necessary or minimal), `c` covering the root `p` in `S`
and `d` labelled `⊤` in `p`, some family `ℓ₀` is a least lift labelling at every rooted cover of
`c` in `S`, and for every `n`, `n` is at most the stable offset exactly when some rooted cover
`(m, q, f)` of `c` in `S` has `q` restricting to `p` along `f` and `β + n ≤ ℓ₀ x e` at a cell `e`
of `q` transported from `d`. -/
theorem exists_natCast_le_stableOffset_iff_exists_isLeast (hS : S.HasLegalTypes)
    (hlim : IsSuccLimit β) (hα : β + ω ≤ α) (hc : S.Covers p c) (hd : p.label d = ⊤) :
    ∃ ℓ₀ : ∀ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), Fin x.2.1.card → Label.{u},
      (∀ x, S.ExtendsToCover c x → IsLeast {ℓ | x.2.1.IsLiftLabelling α ℓ} (ℓ₀ x)) ∧
        ∀ n : ℕ, (n : ℕ∞) ≤ S.stableOffset α hβ c p d ↔
          ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m), S.ExtendsToCover c x ∧
            StageType.restrictFace x.2.2 x.2.1 = some p ∧ ∃ e : Fin x.2.1.card,
              (∀ i : Fin (x.2.1.toScheme.comap x.2.2).card, (i : ℕ) = d →
                x.2.1.cellMap x.2.2 i = e) ∧ ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ x e := by
  obtain ⟨ℓ₀, hleast⟩ := exists_isLeast_isLiftLabelling_family hS hlim hα c
  exact ⟨ℓ₀, hleast, fun _ ↦ natCast_le_stableOffset_iff_exists_isLeast ℓ₀ hc hd hleast⟩

/-- **At consecutive block stages.**  Let `R` be a realization at `λ_{η+1}` with legal types,
`S := R↓λ_η` its reduction, `c` covering the root `p` in `S` and `d` labelled `⊤` in `p`.  Then
some family `ℓ₀` is a least lift labelling to `λ_{η+1}` at every rooted cover of `c` in `S`, and
`n` is at most the stable offset of `d` at `c` in `S` exactly when some rooted cover `(m, q, f)`
of `c` in `S` has `q` restricting to `p` along `f` and `λ_η + n ≤ ℓ₀ x e` at a cell `e` of `q`
transported from `d`.  The sufficient premises for the existence of the least lifts hold here:
`R.HasLegalTypes` passes to the reduction, `λ_η` is a limit, and `λ_{η+1} = λ_η + ω`. -/
theorem exists_natCast_le_stableOffset_reduce_iff_exists_isLeast {η : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage (η + 1)) M} (hl : R.HasLegalTypes)
    {p : StageType.{u} (blockStage η) k} {d : Fin p.card}
    (hc : (R.reduce (isSuccPrelimit_blockStage η)).Covers p c) (hd : p.label d = ⊤) :
    ∃ ℓ₀ : ∀ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
        Fin x.2.1.card → Label.{u},
      (∀ x, (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x →
        IsLeast {ℓ | x.2.1.IsLiftLabelling (blockStage (η + 1)) ℓ} (ℓ₀ x)) ∧
        ∀ n : ℕ, (n : ℕ∞) ≤ (R.reduce (isSuccPrelimit_blockStage η)).stableOffset
            (blockStage (η + 1)) (isSuccPrelimit_blockStage η) c p d ↔
          ∃ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
            (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x ∧
            StageType.restrictFace x.2.2 x.2.1 = some p ∧ ∃ e : Fin x.2.1.card,
              (∀ i : Fin (x.2.1.toScheme.comap x.2.2).card, (i : ℕ) = d →
                x.2.1.cellMap x.2.2 i = e) ∧
              ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ x e :=
  exists_natCast_le_stableOffset_iff_exists_isLeast (hl.reduce _) (isSuccLimit_blockStage η)
    (blockStage_add_one η).ge hc hd

end Realization

end VaughtConjecture

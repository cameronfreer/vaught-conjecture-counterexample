/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate
import VaughtConjecture.Extension.SmallArityExamples
import VaughtConjecture.Label.StepWitness

/-!
# Synchronizing cofaces and twin ordering are refuted

Negative special cases for availability of the stable section at twins
(`VaughtConjecture.Continuation.Candidate`): the hypotheses on single stage types examined for it
are false.  Each is defined in this file only, and no statement elsewhere assumes one.

**Synchronizing cofaces** at a stage `β` would transfer forcing from a cell `a` to a cell `b`
through one more point: for a legal stage type `q` at `β` and cells `a`, `b` with the scope of `a`
in that of `b` and equal grades, some scheme `S` on one more point carries a legal coface of `q`,
and every lawful section of the rows of `S` is at least as large at `b` as at `a`.  Three forms are
refuted:

* **unrestricted** (`UnrestrictedSynchronizingCofaces`, no requirement on the labels of `a` and
  `b`), false at `ω` in universe `0` (`not_unrestrictedSynchronizingCofaces`): the labels of a
  member of the coface family are a lawful section of `S` extending those of `q`, so the statement
  forces `q.label a ≤ q.label b`, and the legal stage type with labels `(⊥, 1)` at two cells of one
  graded index of `SmallArityExamples.onePointScheme 2` refutes it;
* **at cells labelled the formal top** (`SynchronizingCofaces`), false at every stage `β ≥ ω`,
  in particular at every block stage (`not_synchronizingCofaces_blockStage`): by bountifulness of
  the scheme of a legal coface (cap `⊥`), every lawful section of the rows of `q` extends to a
  lawful section of `S`, so the statement forces `ℓ a ≤ ℓ b` for every such `ℓ`; the reduction to
  `β` of the stage type at `ω + ω` with labels `(ω + 1, ω + 2)` on the same scheme has both cells
  labelled the formal top, and its lift `(ω + 1, ω + 2)` refutes it;
* **on lifts** (`SynchronizingCofacesOnLifts`, only the lawful sections of `S` at `β + ω` that lift
  a member of the coface family), false at `ω` (`not_synchronizingCofacesOnLifts`): extend the
  same lift to `S`, collapse it above `ω + 3`, and reduce it to a member of the family.

In each case the two cells share a graded index, so the counterexample is a pair of twins.  By the
argument above, the coface that adds one cell of the grade of `a`, alone at its graded index, with
a tie from its row to `b`, cannot be legal on these stage types: if it were, bountifulness would
extend to its rows the lift `(ω + 1, ω + 2)`, larger at `a` than at `b`, which the tie excludes.

**Twin ordering** at `β` (`TwinOrdering`) asks, for a legal stage type `q` at `β` and cells `s₀`,
`t₀` labelled the formal top with the scope of `s₀` strictly inside that of `t₀` and equal grades,
for one cell labelled the formal top at the graded index of `t₀` that is at least as large as `s₀`
in every lift of `q` to `β + ω`.  It is false at every stage that is zero or a limit
(`not_twinOrdering`), in particular at every block stage (`not_twinOrdering_blockStage`).  The
special case is a legal scheme on `Fin 2` with five cells: `0` of scope `{0}`, `1` of scope `{1}`,
the twins `2`, `3` of scope `univ`, all of grade `1`, and `4` of scope `univ` and grade `2`; its
rows are `ω + 2` at `0`, `⊥` at `1` and `4`, and `(ω + 2, ⊥, ω + 2, 1)` and `(ω + 2, ⊥, 1, ω + 2)`
at the twins.  A section is lawful when it is `⊥` at `1` and `4` and self-visible at `1` at `0`
and the twins, each twin is at most `0`, and `0` is at most the larger twin.  Locality uses a
shifter with three values, `⊥` on `⊥`, one value on the other labels below `ω`, and one from `ω`
on, which commutes with every visibility replacement.  Bountifulness reduces to two capped lifts,
from `({0}, 1)` and from `({1}, 1)` to `(univ, 1)`.  For `β` zero or a limit, the lifts
`(β + 2, ⊥, β + 2, β + 1, ⊥)` and `(β + 2, ⊥, β + 1, β + 2, ⊥)` reduce to the same legal type at
`β`, with `0` and both twins labelled the formal top.  On that type every lift sets `0` to the
larger twin, and both orders of the twins occur, so no cell at the graded index of the twins is at
least `0` in every lift.  Hence no hypothesis that orders a twin above `s₀` in all lifts of a
single type can hold.

**The lesson.**  Availability of the stable section at twins is nevertheless proved, for every
realization with legal types (`Realization.availability_stableSection_of_hasLegalTypes`, in
`VaughtConjecture.Continuation.Candidate`).  The transfer happens inside the forcing cover: a legal
rooted cover that forces a level at `s₀` forces it, over the same cover, at a cell labelled the
formal top at the graded index of `t₀` (`StageType.exists_forcesThreshold_twin_face`).  The
statements refuted here compare the cells in every lift and ignore the forced level.  On the
five-cell type the forced level at `0` is its grade `1`: it is at least the grade by the order law,
and at most `1` because `0` and the twins, the cells labelled the formal top, have grade `1`, so the
capped lift with `K = 1` is a lift of the type (`StageType.capLift_reduce`).  Both twins also have
level `1` by the order law, while the lifts order the twins both ways above that level.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Continuation.CandidateCounterexamples

open Finset Ordinal StageType CellScheme Label SmallArityExamples

/-! ### Three forms of synchronizing cofaces -/

/-- **Unrestricted synchronizing cofaces** at `β`, with no requirement on the labels of the two
cells.  Refuted at `ω` in universe `0` (`not_unrestrictedSynchronizingCofaces`). -/
def UnrestrictedSynchronizingCofaces (β : Ordinal.{u}) : Prop :=
  ∀ ⦃m : ℕ⦄ (q : StageType.{u} β m), q.IsLegal → ∀ a b : Fin q.card,
    q.toCellScheme.scope a ⊆ q.toCellScheme.scope b →
      q.toCellScheme.grade a = q.toCellScheme.grade b →
        ∃ S : Scheme.{u} (m + 1), (q.cofaces ∩ saturationFamily S).Nonempty ∧
          ∀ ρ : Fin S.card → Label.{u}, S.rows.IsLawful ρ →
            ∀ a' b' : Fin (S.comap Fin.castSuccEmb).card, (a' : ℕ) = a → (b' : ℕ) = b →
              ρ (S.cellMap Fin.castSuccEmb a') ≤ ρ (S.cellMap Fin.castSuccEmb b')

/-- **Synchronizing cofaces** at `β`, at two cells labelled the formal top.  Refuted at every
stage `β ≥ ω` (`not_synchronizingCofaces`). -/
def SynchronizingCofaces (β : Ordinal.{u}) : Prop :=
  ∀ ⦃m : ℕ⦄ (q : StageType.{u} β m), q.IsLegal → ∀ a b : Fin q.card,
    q.toCellScheme.scope a ⊆ q.toCellScheme.scope b →
      q.toCellScheme.grade a = q.toCellScheme.grade b → q.label a = ⊤ → q.label b = ⊤ →
        ∃ S : Scheme.{u} (m + 1), (q.cofaces ∩ saturationFamily S).Nonempty ∧
          ∀ ρ : Fin S.card → Label.{u}, S.rows.IsLawful ρ →
            ∀ a' b' : Fin (S.comap Fin.castSuccEmb).card, (a' : ℕ) = a → (b' : ℕ) = b →
              ρ (S.cellMap Fin.castSuccEmb a') ≤ ρ (S.cellMap Fin.castSuccEmb b')

/-- **Synchronizing cofaces on lifts** at `β`: as `SynchronizingCofaces`, but only for the lawful
sections `ρ` of the rows of `S` at the stage `β + ω` whose reduction to `β` is the label section
of a member of the coface family.  Refuted at `ω` (`not_synchronizingCofacesOnLifts`). -/
def SynchronizingCofacesOnLifts (β : Ordinal.{u}) : Prop :=
  ∀ ⦃m : ℕ⦄ (q : StageType.{u} β m), q.IsLegal → ∀ a b : Fin q.card,
    q.toCellScheme.scope a ⊆ q.toCellScheme.scope b →
      q.toCellScheme.grade a = q.toCellScheme.grade b → q.label a = ⊤ → q.label b = ⊤ →
        ∃ S : Scheme.{u} (m + 1), (q.cofaces ∩ saturationFamily S).Nonempty ∧
          ∀ ρ : Fin S.card → Label.{u}, S.rows.IsLawful ρ → (∀ d, AtStage (β + ω) (ρ d)) →
            (∃ D ∈ q.cofaces ∩ saturationFamily S, ∀ (i : Fin D.card) (j : Fin S.card),
              (i : ℕ) = j → D.label i = Label.reduce β (ρ j)) →
            ∀ a' b' : Fin (S.comap Fin.castSuccEmb).card, (a' : ℕ) = a → (b' : ℕ) = b →
              ρ (S.cellMap Fin.castSuccEmb a') ≤ ρ (S.cellMap Fin.castSuccEmb b')

/-! ### What a coface forces -/

/-- Unrestricted synchronizing cofaces force `q.label a ≤ q.label b`: the labels of a member of
the coface family are a lawful section of `S` extending those of `q`. -/
private theorem label_le_of_unrestrictedSynchronizingCofaces {β : Ordinal.{u}}
    (h : UnrestrictedSynchronizingCofaces β) {m : ℕ} (q : StageType.{u} β m) (hq : q.IsLegal)
    (a b : Fin q.card) (hab : q.toCellScheme.scope a ⊆ q.toCellScheme.scope b)
    (hg : q.toCellScheme.grade a = q.toCellScheme.grade b) : q.label a ≤ q.label b := by
  obtain ⟨S, ⟨D, ⟨-, hD⟩, hDS⟩, hρ⟩ := h q hq a b hab hg
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hD
  have hDS' : D.toScheme = S := hDS
  subst hDS'
  exact hρ D.label D.isLawful a b rfl rfl

/-- Synchronizing cofaces force `ℓ a ≤ ℓ b` for every lawful section `ℓ` of the rows of `q`: by
bountifulness of the scheme of the coface (cap `⊥`), `ℓ` extends to a lawful section of `S`. -/
private theorem lawful_le_of_synchronizingCofaces {β : Ordinal.{u}} (h : SynchronizingCofaces β)
    {m : ℕ} (q : StageType.{u} β m) (hq : q.IsLegal) (a b : Fin q.card)
    (hab : q.toCellScheme.scope a ⊆ q.toCellScheme.scope b)
    (hg : q.toCellScheme.grade a = q.toCellScheme.grade b) (ha : q.label a = ⊤)
    (hb : q.label b = ⊤) (ℓ : Fin q.card → Label.{u}) (hℓ : q.rows.IsLawful ℓ) : ℓ a ≤ ℓ b := by
  obtain ⟨S, ⟨D, ⟨hDl, hD⟩, hDS⟩, hρ⟩ := h q hq a b hab hg ha hb
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hD
  have hDS' : D.toScheme = S := hDS
  subst hDS'
  obtain ⟨r, hr, -, hext⟩ := Scheme.IsLegal.exists_isLawful_extend (c := ⊥) hDl hf
    (isSelfVisible_bot _) hℓ D.isLawful (fun _ ↦ by simp)
  exact (hext a).symm.trans_le ((hρ r hr a b rfl rfl).trans_eq (hext b))

/-! ### Two cells of one graded index labelled `⊥` and `1` -/

/-- The labels `(⊥, 1)`. -/
private noncomputable def botOne : Fin 2 → Label.{0} := ![⊥, 1]

private theorem monotone_botOne : Monotone botOne := fun i j hij ↦ by
  fin_cases i <;> fin_cases j <;> simp_all [botOne]

private theorem isSelfVisible_botOne (i : Fin 2) : IsSelfVisible 1 (botOne i) := by
  fin_cases i
  · simp [botOne]
  · -- the label of `botOne` at `1`
    change IsSelfVisible 1 (1 : Label.{0})
    simp

private theorem isLegal_botOne : (onePointScheme 2 botOne).IsLegal :=
  isLegal_onePointScheme (by decide) monotone_botOne (fun i ↦ by
    fin_cases i
    · exact WithBot.bot_lt_coe _
    · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp [botOne]⟩)) isSelfVisible_botOne

/-- The legal stage type at `ω` on `onePointScheme 2 (⊥, 1)` with labels `(⊥, 1)`. -/
private noncomputable def typeBotOne : StageType.{0} ω 1 where
  toScheme := onePointScheme 2 botOne
  label := botOne
  isWellFormed := isLegal_botOne.isWellFormed
  isCoded := isLegal_botOne.isCoded
  isLawful :=
    { orderly := isSelfVisible_botOne
      locality := fun s ↦
        (TransformsTo.refl _ _).min_const (K := 1) (fun _ ↦ le_rfl) (isSelfVisible_botOne s)
      availability := fun s _ _ _ ↦ ⟨⟨1, by decide⟩, rfl, monotone_botOne (Fin.le_last s)⟩ }
  atStage i := by
    fin_cases i
    · exact atStage_bot
    · left
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by simp [one_lt_omega0]))

/-- **Unrestricted synchronizing cofaces are false at `ω`**, in universe `0` only (the refuting
stage type has labels in `Label.{0}`): they would give `1 ≤ ⊥`. -/
theorem not_unrestrictedSynchronizingCofaces : ¬ UnrestrictedSynchronizingCofaces.{0} ω :=
  fun h ↦ by
    have := label_le_of_unrestrictedSynchronizingCofaces h typeBotOne isLegal_botOne
      ⟨1, by decide⟩ ⟨0, by decide⟩ subset_rfl rfl
    -- the labels of `typeBotOne` at the two cells
    change (1 : Label.{0}) ≤ ⊥ at this
    exact WithBot.one_ne_bot (le_bot_iff.mp this)

/-! ### Two cells of one graded index labelled the formal top -/

/-- The labels `(ω + 1, ω + 2)`. -/
private noncomputable def twinRows (i : Fin 2) : Label.{u} :=
  ((ω + ((i : ℕ) + 1 : ℕ) : Ordinal.{u}) : Label.{u})

private theorem monotone_twinRows : Monotone twinRows := fun i j hij ↦
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (add_le_add_right (Nat.cast_le.mpr (by
    have : (i : ℕ) ≤ j := hij
    omega)) ω))

private theorem isSelfVisible_twinRows (i : Fin 2) : IsSelfVisible 1 (twinRows.{u} i) :=
  isSelfVisible_coe_add isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem isLegal_twinRows : (onePointScheme 2 twinRows.{u}).IsLegal :=
  isLegal_onePointScheme (by decide) monotone_twinRows
    (fun i ↦ lt_omega0_sq_iff.mpr (.inr ⟨1, (i : ℕ) + 1, by simp [twinRows]⟩))
    isSelfVisible_twinRows

private theorem isLawful_twinRows : (onePointScheme 2 twinRows.{u}).rows.IsLawful twinRows :=
  { orderly := isSelfVisible_twinRows
    locality := fun s ↦
      (TransformsTo.refl _ _).min_const (K := 1) (fun _ ↦ le_rfl) (isSelfVisible_twinRows s)
    availability := fun s _ _ _ ↦ ⟨⟨1, by decide⟩, rfl, monotone_twinRows (Fin.le_last s)⟩ }

/-- The stage type at `ω + ω` with labels `(ω + 1, ω + 2)`. -/
private noncomputable def twinLift : StageType.{u} (ω + ω) 1 where
  toScheme := onePointScheme 2 twinRows
  label := twinRows
  isWellFormed := isLegal_twinRows.isWellFormed
  isCoded := isLegal_twinRows.isCoded
  isLawful := isLawful_twinRows
  atStage _ := .inl (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    (add_lt_add_right (natCast_lt_omega0 _) ω)))

/-- Its reduction, read at a stage `β ≥ ω`: two cells of one graded index labelled the formal
top. -/
private noncomputable def twinType {β : Ordinal.{u}} (hβ : ω ≤ β) : StageType.{u} β 1 :=
  (twinLift.reduce isSuccLimit_omega0.isSuccPrelimit).castLE hβ

private theorem twinType_label {β : Ordinal.{u}} (hβ : ω ≤ β) (i : Fin 2) :
    (twinType hβ).label i = ⊤ :=
  Label.reduce_of_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))

/-- **Synchronizing cofaces are false at every stage `β ≥ ω`**: they would order the lift
`(ω + 1, ω + 2)` the other way. -/
theorem not_synchronizingCofaces {β : Ordinal.{u}} (hβ : ω ≤ β) :
    ¬ SynchronizingCofaces.{u} β := fun h ↦ by
  have := lawful_le_of_synchronizingCofaces h (twinType hβ) isLegal_twinRows
    (⟨1, by decide⟩ : Fin 2) (⟨0, by decide⟩ : Fin 2) subset_rfl rfl (twinType_label hβ _)
    (twinType_label hβ _) twinRows isLawful_twinRows
  have h' := Nat.cast_le.mp ((add_le_add_iff_left ω).mp
    (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)))
  simp at h'

/-- **Synchronizing cofaces are false at every block stage.** -/
theorem not_synchronizingCofaces_blockStage (ξ : Ordinal.{u}) :
    ¬ SynchronizingCofaces.{u} (blockStage ξ) :=
  not_synchronizingCofaces (omega0_le_blockStage ξ)

/-- No model at a block stage comes with synchronizing cofaces. -/
example {M : Type v} {ξ : Ordinal.{u}} (R : Realization.{u, v} (blockStage ξ) M) :
    ¬ (R.IsModel ∧ SynchronizingCofaces.{u} (blockStage ξ)) :=
  fun h ↦ not_synchronizingCofaces_blockStage ξ h.2

/-! ### Synchronizing cofaces on lifts -/

private theorem exists_isLawful_of_eq {P : Scheme.{u} 1} (h : P = onePointScheme 2 twinRows) :
    ∃ ℓ : Fin P.card → Label.{u}, P.rows.IsLawful ℓ ∧
      ∀ (i : Fin P.card) (j : Fin 2), (i : ℕ) = j → ℓ i = twinRows j := by
  subst h
  exact ⟨twinRows, isLawful_twinRows, fun i j hij ↦ congrArg twinRows (Fin.ext hij)⟩

/-- **Synchronizing cofaces on lifts are false at `ω`**: the lift `(ω + 1, ω + 2)`, extended to
the scheme of a member of the coface family and collapsed above `ω + 3`, lifts a member of the
family and orders the two cells the other way. -/
theorem not_synchronizingCofacesOnLifts : ¬ SynchronizingCofacesOnLifts.{u} ω := fun h ↦ by
  have hω : Order.IsSuccPrelimit (ω : Ordinal.{u}) := isSuccLimit_omega0.isSuccPrelimit
  set q0 := twinType (le_refl (ω : Ordinal.{u}))
  obtain ⟨S, ⟨D, ⟨hDl, hD⟩, hDS⟩, hρ⟩ := h q0 isLegal_twinRows (⟨1, by decide⟩ : Fin 2)
    (⟨0, by decide⟩ : Fin 2) subset_rfl rfl (twinType_label _ _) (twinType_label _ _)
  have hDS' : D.toScheme = S := hDS
  subst hDS'
  obtain ⟨hf, heq⟩ := (restrictFace_eq_some_iff _ _).mp hD
  have hS' : D.toScheme.comap Fin.castSuccEmb = onePointScheme 2 twinRows :=
    congrArg toScheme heq
  obtain ⟨ℓ, hℓ, hℓr⟩ := exists_isLawful_of_eq hS'
  obtain ⟨r', hr', -, hext⟩ := Scheme.IsLegal.exists_isLawful_extend (c := ⊥) hDl hf
    (isSelfVisible_bot _) hℓ D.isLawful (fun _ ↦ by simp)
  -- the collapse of the extension above `ω + 3`
  set ρ : Fin D.card → Label.{u} := fun d ↦ collapse ω 3 (r' d)
  have hρl : D.toScheme.rows.IsLawful ρ :=
    { orderly := fun d ↦ (hr'.orderly d).reduce _
      locality := fun s ↦ by
        have := (hr'.locality s).collapse hω (K := 2) (N := 3)
          (fun d : D.toCellScheme.below (D.toCellScheme.gradedIndex s) ↦ D.grade_le d.1)
          (by decide)
        convert this using 1
        funext e
        exact ((monotone_reduce _).map_min).symm
      availability := fun s t h₁ h₂ ↦ by
        obtain ⟨w, hw, hle⟩ := hr'.availability s t h₁ h₂
        exact ⟨w, hw, monotone_reduce _ hle⟩ }
  have hρat : ∀ d, AtStage (ω + ω) (ρ d) := fun d ↦ (atStage_reduce _ _).mono
    (add_le_add_right (natCast_lt_omega0 3).le ω)
  have hred : ∀ d, Label.reduce ω (ρ d) = Label.reduce ω (r' d) := fun d ↦
    reduce_reduce_of_le le_self_add (r' d)
  -- the member of the coface family that it lifts
  let D' : StageType.{u} ω 2 :=
    { toScheme := D.toScheme
      label := Label.reduce ω ∘ ρ
      isWellFormed := D.isWellFormed
      isCoded := D.isCoded
      isLawful := hρl.reduce hω
      atStage := fun _ ↦ atStage_reduce _ _ }
  have hcard : (D.toScheme.comap Fin.castSuccEmb).card = 2 := congrArg Scheme.card hS'
  have hD' : D' ∈ q0.cofaces ∩ saturationFamily D.toScheme := by
    refine ⟨⟨hDl, (restrictFace_eq_some_iff _ _).mpr ⟨hf, StageType.ext (by rw [← heq]; rfl)
      fun i j hij ↦ ?_⟩⟩, rfl⟩
    -- the label of `D'` at the cell of `q0` indexed by `i`
    change Label.reduce ω (ρ (D.cellMap Fin.castSuccEmb i)) = q0.label j
    have e1 : r' (D.cellMap Fin.castSuccEmb i) = ℓ i := hext i
    rw [hred, e1]
    refine Eq.trans ?_ (twinType_label (le_refl _) j).symm
    obtain ⟨j, hj⟩ := j
    rw [hℓr i ⟨j, (hj : j < 2)⟩ hij]
    exact Label.reduce_of_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))
  have := hρ ρ hρl hρat ⟨D', hD', fun i j hij ↦ by rw [Fin.ext hij]; rfl⟩
    ⟨1, by omega⟩ ⟨0, by omega⟩ rfl rfl
  simp only [ρ, hext] at this
  rw [hℓr _ ⟨1, by decide⟩ rfl, hℓr _ ⟨0, by decide⟩ rfl] at this
  have h3 : ∀ n : ℕ, n < 3 → collapse ω 3 ((ω + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) =
      ((ω + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := fun n hn ↦
    reduce_of_lt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (add_lt_add_right (Nat.cast_lt.mpr hn) ω)))
  -- unfold the two labels `ω + 2` and `ω + 1` of the lift
  change collapse ω 3 ((ω + ((1 + 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤
    collapse ω 3 ((ω + ((0 + 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) at this
  rw [h3 _ (by decide), h3 _ (by decide)] at this
  have h' := Nat.cast_le.mp ((add_le_add_iff_left ω).mp
    (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)))
  simp at h'

/-! ### Twin ordering -/

/-- **Twin ordering** at the stage `β`: for every legal stage type `q` at `β` and cells `s₀`, `t₀`
of `q` labelled the formal top, with the scope of `s₀` strictly inside that of `t₀` and equal
grades, some cell `w` labelled the formal top at the graded index of `t₀` is at least as large as
`s₀` in every **lift** of `q` to `β + ω`, that is, every lawful section of the rows of `q` at the
stage `β + ω` reducing at `β` to the labels of `q`.  It would give availability of the stable
section at twins.  Refuted at every stage that is zero or a limit (`not_twinOrdering`). -/
def TwinOrdering (β : Ordinal.{u}) : Prop :=
  ∀ ⦃m : ℕ⦄ (q : StageType.{u} β m), q.IsLegal → ∀ s₀ t₀ : Fin q.card,
    q.toCellScheme.scope s₀ ⊂ q.toCellScheme.scope t₀ →
      q.toCellScheme.grade s₀ = q.toCellScheme.grade t₀ → q.label s₀ = ⊤ → q.label t₀ = ⊤ →
        ∃ w, q.toCellScheme.gradedIndex w = q.toCellScheme.gradedIndex t₀ ∧ q.label w = ⊤ ∧
          ∀ ℓ : Fin q.card → Label.{u}, q.rows.IsLawful ℓ →
            (∀ d, Label.AtStage (β + ω) (ℓ d)) → (∀ d, Label.reduce β (ℓ d) = q.label d) →
              ℓ s₀ ≤ ℓ w

/-! ### A shifter with three values -/

/-- The label `ω + 2`. -/
private noncomputable abbrev omegaAddTwo : Label.{u} :=
  ((ω + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

private theorem one_lt_coe_omega0 : (1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  simp

private theorem not_omegaAddTwo_lt : ¬ omegaAddTwo.{u} < ((ω : Ordinal.{u}) : Label.{u}) :=
  fun h ↦ (not_lt.mpr le_self_add) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))

private theorem one_le_omegaAddTwo : (1 : Label.{u}) ≤ omegaAddTwo.{u} :=
  one_lt_coe_omega0.le.trans (not_lt.mp not_omegaAddTwo_lt)

private theorem isSelfVisible_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add isSuccLimit_omega0.isSuccPrelimit (by omega)

/-- The shifter sending `⊥` to `⊥`, every other label below `ω` to `m`, and every label at least
`ω` to `a`. -/
private noncomputable def threeValueShifter (a m x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then (if x = ⊥ then ⊥ else m) else a

/-- The shifter is invariant under visibility replacement. -/
private theorem threeValueShifter_visibilityReplace (a m x : Label.{u}) (k i : ℕ) :
    threeValueShifter a m (visibilityReplace k i x) = threeValueShifter a m x := by
  simp only [threeValueShifter, Label.visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit,
    visibilityReplace_eq_bot_iff]

private theorem isWitness_threeValueShifter {a m : Label.{u}} (ha : IsSelfVisible 1 a)
    (hm : IsSelfVisible 1 m) (hma : m ≤ a) :
    IsWitness (stepSuppressor 1) (threeValueShifter a m) where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := by simp [threeValueShifter, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    simp only [threeValueShifter]
    by_cases hy : y < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
      by_cases hx0 : x = ⊥
      · rw [ite_eq_left hx0]
        exact bot_le
      · rw [ite_eq_right hx0,
          ite_eq_right (show ¬ y = ⊥ from fun h ↦ hx0 (le_bot_iff.mp (h ▸ hxy)))]
    · rw [ite_eq_right hy]
      split_ifs <;> first | exact bot_le | exact hma | exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    rw [threeValueShifter_visibilityReplace]
    have hsv : IsSelfVisible 1 (threeValueShifter a m x) := by
      simp only [threeValueShifter]
      split_ifs
      exacts [isSelfVisible_bot _, hm, ha]
    by_cases hk : k ≤ 1
    · exact ((hsv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]

/-- Rows of grade `1` with values `⊥`, `1`, `ω + 2` transform to sections with values `⊥`, `m`,
`a` at the same cells, through the three-valued shifter and the step suppressor at `1`. -/
private theorem transformsTo_threeValueShifter {D : Type*} {grade : D → ℕ}
    (hg : ∀ d, grade d = 1) {r t : D → Label.{u}} {a m : Label.{u}} (ha : IsSelfVisible 1 a)
    (hm : IsSelfVisible 1 m) (hma : m ≤ a)
    (h : ∀ d, (r d = ⊥ ∧ t d = ⊥) ∨ (r d = 1 ∧ t d = m) ∨ (r d = omegaAddTwo ∧ t d = a)) :
    TransformsTo grade r t :=
  ⟨_, _, isWitness_threeValueShifter ha hm hma, fun d ↦ by
    rw [hg d, stepSuppressor_of_le le_rfl, min_top_right]
    rcases h d with ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hr, ht⟩ <;> rw [hr, ht, threeValueShifter]
    · simp [WithBot.bot_lt_coe]
    · rw [ite_eq_left one_lt_coe_omega0, ite_eq_right (by simp)]
    · rw [ite_eq_right not_omegaAddTwo_lt]⟩

/-! ### A legal scheme on two points with five cells -/

/-- The cells on `Fin 2`, with faces the intervals: `0` of scope `{0}`, `1` of scope `{1}`, `2`
and `3` (the twins) of scope `univ`, all of grade `1`, and `4` of scope `univ` and grade `2`. -/
private def fiveCells : CellScheme (Fin 5) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ, univ], ![1, 1, 1, 1, 2]⟩

/-- The rows: `ω + 2` at `0`; `⊥` at `1` and `4`; `(ω + 2, ⊥, ω + 2, 1)` at `2` and
`(ω + 2, ⊥, 1, ω + 2)` at `3`, on the cells `0`–`3`. -/
private noncomputable def fiveCellRows : Fin 5 → Fin 5 → Label.{u} :=
  ![fun _ ↦ omegaAddTwo, fun _ ↦ ⊥, ![omegaAddTwo, ⊥, omegaAddTwo, 1, ⊥],
    ![omegaAddTwo, ⊥, 1, omegaAddTwo, ⊥], fun _ ↦ ⊥]

private noncomputable abbrev fiveCellScheme : Scheme.{u} 2 :=
  ⟨5, fiveCells, ⟨fun s d ↦ fiveCellRows s d.1⟩⟩

private theorem fiveCellScheme_row (s : Fin 5) (d) :
    fiveCellScheme.{u}.rows.row s d = fiveCellRows s d.1 :=
  rfl

/-- **Lawful sections**, sufficient conditions: `⊥` at `1` and `4`, self-visible at `1` at `0`,
`2`, `3`, the twins at most `0`, and `0` at most the larger twin. -/
private theorem isLawful_fiveCellScheme {w : Fin 5 → Label.{u}} (h1 : w 1 = ⊥) (h4 : w 4 = ⊥)
    (hv0 : IsSelfVisible 1 (w 0)) (hv2 : IsSelfVisible 1 (w 2)) (hv3 : IsSelfVisible 1 (w 3))
    (h20 : w 2 ≤ w 0) (h30 : w 3 ≤ w 0) (h0 : w 0 ≤ max (w 2) (w 3)) :
    fiveCellScheme.{u}.rows.IsLawful w where
  orderly d := by
    fin_cases d
    · exact hv0
    · -- the section at the cell `1`
      change IsSelfVisible _ (w 1)
      rw [h1]
      exact isSelfVisible_bot _
    · exact hv2
    · exact hv3
    · -- the section at the cell `4`
      change IsSelfVisible _ (w 4)
      rw [h4]
      exact isSelfVisible_bot _
  locality s := by
    fin_cases s
    · refine transformsTo_threeValueShifter (a := w 0) (m := ⊥) ?_ hv0 (isSelfVisible_bot _)
        bot_le ?_
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 0 ∧ fiveCells.grade d ≤ fiveCells.grade 0 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells]
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 0 ∧ fiveCells.grade d ≤ fiveCells.grade 0 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells, fiveCellRows]
    · convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the cell `1`
      change min _ (w 1) = ⊥
      rw [h1, min_bot_right]
    · refine transformsTo_threeValueShifter (a := w 2) (m := min (w 3) (w 2)) ?_ hv2
        (hv3.min hv2) (min_le_right _ _) ?_
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 2 ∧ fiveCells.grade d ≤ fiveCells.grade 2 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells]
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 2 ∧ fiveCells.grade d ≤ fiveCells.grade 2 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells, fiveCellRows]
    · refine transformsTo_threeValueShifter (a := w 3) (m := min (w 2) (w 3)) ?_ hv3
        (hv2.min hv3) (min_le_right _ _) ?_
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 3 ∧ fiveCells.grade d ≤ fiveCells.grade 3 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells]
      · rintro ⟨d, hd⟩
        have hd' : fiveCells.scope d ⊆ fiveCells.scope 3 ∧ fiveCells.grade d ≤ fiveCells.grade 3 :=
          hd
        fin_cases d <;> first | exact absurd hd' (by decide) | simp_all [fiveCells, fiveCellRows]
    · convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the cell `4`
      change min _ (w 4) = ⊥
      rw [h4, min_bot_right]
  availability s t hst hg := by
    have key : ∀ s t : Fin 5, fiveCells.scope s ⊆ fiveCells.scope t →
        fiveCells.grade s = fiveCells.grade t →
          fiveCells.gradedIndex s = fiveCells.gradedIndex t ∨ (s = 0 ∨ s = 1) ∧ (t = 2 ∨ t = 3) :=
      by decide
    rcases key s t hst hg with h | ⟨hs, ht⟩
    · exact ⟨s, h, le_rfl⟩
    · have hgi : fiveCells.gradedIndex 2 = fiveCells.gradedIndex t ∧
          fiveCells.gradedIndex 3 = fiveCells.gradedIndex t := by
        rcases ht with rfl | rfl <;> decide
      rcases hs with rfl | rfl
      · rcases le_max_iff.mp h0 with h | h
        exacts [⟨2, hgi.1, h⟩, ⟨3, hgi.2, h⟩]
      · exact ⟨2, hgi.1, by rw [h1]; exact bot_le⟩

private theorem isLawfulBelow_fiveCellScheme {w : Fin 5 → Label.{u}}
    (h : fiveCellScheme.{u}.rows.IsLawful w) (X : Finset (Fin 2) × ℕ) :
    fiveCellScheme.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: `⊥` at `1`, self-visible at `1`
at `0`, `2`, `3`, the twins at most `0`, and `0` at most the larger twin. -/
private theorem conditions_of_isLawfulBelow {w : Fin 5 → Label.{u}}
    (hq : fiveCellScheme.{u}.rows.IsLawfulBelow (univ, 1) (fun d ↦ w d)) :
    w 1 = ⊥ ∧ IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 2) ∧ IsSelfVisible 1 (w 3) ∧
      w 2 ≤ w 0 ∧ w 3 ≤ w 0 ∧ w 0 ≤ max (w 2) (w 3) := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 5, i ≠ 4 → fiveCells.gradedIndex i ≤ ((univ : Finset (Fin 2)), 1) := by
    decide
  have self : ∀ i : Fin 5, fiveCells.gradedIndex i ≤ fiveCells.gradedIndex i := fun i ↦ le_rfl
  refine ⟨?_, ho 0 (m 0 (by decide)), ho 2 (m 2 (by decide)), ho 3 (m 3 (by decide)), ?_, ?_, ?_⟩
  · have := (hl 1 (m 1 (by decide))).eq_bot (d := ⟨1, self 1⟩) rfl
    simpa using this
  · have := (hl 2 (m 2 (by decide))).le_of_le (d := ⟨2, self 2⟩)
      (d' := ⟨0, show fiveCells.gradedIndex 0 ≤ fiveCells.gradedIndex 2 by decide⟩) le_rfl le_rfl
    simpa using (le_min_iff.mp this).1
  · have := (hl 3 (m 3 (by decide))).le_of_le (d := ⟨3, self 3⟩)
      (d' := ⟨0, show fiveCells.gradedIndex 0 ≤ fiveCells.gradedIndex 3 by decide⟩) le_rfl le_rfl
    simpa using (le_min_iff.mp this).1
  · obtain ⟨u, hu, hle⟩ := ha 0 2 (m 2 (by decide)) (by decide) rfl
    have : ∀ u : Fin 5, fiveCells.gradedIndex u = fiveCells.gradedIndex 2 → u = 2 ∨ u = 3 := by
      decide
    rcases this u hu with rfl | rfl
    exacts [le_max_of_le_left hle, le_max_of_le_right hle]

/-- A section below `(univ, 1)`, extended by `⊥`, is lawful below `(univ, 1)`. -/
private theorem isLawfulBelow_extendBot
    {q : fiveCells.below ((univ : Finset (Fin 2)), 1) → Label.{u}}
    (hq : fiveCellScheme.{u}.rows.IsLawfulBelow (univ, 1) q) :
    fiveCellScheme.{u}.rows.IsLawfulBelow (univ, 1)
      (fun d ↦ CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **The capped lift from `({0}, 1)` to `(univ, 1)`**: given a lawful `q = (x, ⊥, a, b)` below
`(univ, 1)` and a prescription `x'` at `0` agreeing with `x` below the cap `c`, the section
`(x', ⊥, min â x', min b̂ x', ⊥)` is lawful, where `â`, `b̂` are the formal top at labels at least
`c`. -/
private theorem cappedLift_scope_zero
    (h : (({0} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    fiveCellScheme.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨q1, -, hv2, hv3, q20, q30, q0⟩ := conditions_of_isLawfulBelow (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q with hwq
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have m0X : fiveCells.gradedIndex 0 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  set x' := p ⟨0, m0X⟩ with hx'
  have hv0' : IsSelfVisible 1 x' := hp.orderly ⟨0, m0X⟩
  have hcap : min (wq 0) c = min x' c := by
    have := hpq ⟨0, m0X⟩
    rwa [hqw] at this
  let w' : Fin 5 → Label.{u} :=
    ![x', ⊥, min (raise c (wq 2)) x', min (raise c (wq 3)) x', ⊥]
  have hlaw : fiveCellScheme.{u}.rows.IsLawful w' := by
    refine isLawful_fiveCellScheme rfl rfl hv0' ((isSelfVisible_raise c hv2).min hv0')
      ((isSelfVisible_raise c hv3).min hv0') (min_le_right _ _) (min_le_right _ _) ?_
    -- the section `w'` at the cells `0`, `2` and `3`
    change x' ≤ max (min (raise c (wq 2)) x') (min (raise c (wq 3)) x')
    by_cases hcx : c ≤ x'
    · have hc0 : c ≤ wq 0 := by
        rw [min_eq_right hcx] at hcap
        exact min_eq_right_iff.mp hcap
      rcases le_max_iff.mp q0 with h2 | h3
      · rw [show raise c (wq 2) = ⊤ from ite_eq_left (hc0.trans h2), min_top_left]
        exact le_max_left _ _
      · rw [show raise c (wq 3) = ⊤ from ite_eq_left (hc0.trans h3), min_top_left]
        exact le_max_right _ _
    · have hlt : x' < c := not_le.mp hcx
      have h0 : wq 0 = x' := by
        rw [min_eq_left hlt.le] at hcap
        rcases le_total (wq 0) c with h | h
        · rwa [min_eq_left h] at hcap
        · rw [min_eq_right h] at hcap
          exact absurd hcap.symm hlt.ne
      have hh2 : raise c (wq 2) = wq 2 :=
        ite_eq_right (not_le.mpr ((q20.trans_eq h0).trans_lt hlt))
      have hh3 : raise c (wq 3) = wq 3 :=
        ite_eq_right (not_le.mpr ((q30.trans_eq h0).trans_lt hlt))
      rw [hh2, hh3, min_eq_left (q20.trans_eq h0), min_eq_left (q30.trans_eq h0), ← h0]
      exact q0
  refine ⟨fun d ↦ w' d, isLawfulBelow_fiveCellScheme hlaw _, fun d ↦ ?_, fun d ↦ ?_⟩
  · obtain ⟨d, hd⟩ := d
    rw [hqw]
    have hd' : fiveCells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hcap.symm
    · -- `w'` at the cell `1`
      change min ⊥ c = min (wq 1) c
      rw [q1]
    · -- `w'` at the first twin
      change min (min (raise c (wq 2)) x') c = min (wq 2) c
      rw [min_assoc, ← hcap, min_left_comm, min_raise, min_comm,
        min_eq_left ((min_le_left _ _).trans q20)]
    · -- `w'` at the second twin
      change min (min (raise c (wq 3)) x') c = min (wq 3) c
      rw [min_assoc, ← hcap, min_left_comm, min_raise, min_comm,
        min_eq_left ((min_le_left _ _).trans q30)]
    · exact absurd hd' (by decide)
  · obtain ⟨d, hd⟩ := d
    have hd' : fiveCells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 5, fiveCells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) → d = 0 := by
      decide
    obtain rfl := key d hd'
    rfl

/-- **The capped lift from `({1}, 1)` to `(univ, 1)`**: the cell of scope `{1}` is `⊥` in every
lawful section, so the given section is a lift. -/
private theorem cappedLift_scope_one
    (h : (({1} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    fiveCellScheme.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦
    ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
  obtain ⟨d, hd⟩ := d
  have hd' : fiveCells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) := hd
  have key : ∀ d : Fin 5, fiveCells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) → d = 1 := by
    decide
  obtain rfl := key d hd'
  have hq1 := (conditions_of_isLawfulBelow (isLawfulBelow_extendBot hq)).1
  rw [CellScheme.Rows.extendBot_of_mem q
    (show fiveCells.gradedIndex 1 ≤ ((univ : Finset (Fin 2)), 1) by decide)] at hq1
  have hp1 : p ⟨1, hd⟩ = ⊥ := by
    have := (hp.locality ⟨1, hd⟩).eq_bot (d := ⟨⟨1, hd⟩,
      le_refl ((fiveCellScheme.{u}.toCellScheme.reindex Subtype.val).gradedIndex ⟨1, hd⟩)⟩) rfl
    simpa using this
  rw [hp1]
  exact hq1

/-- **The scheme is legal.**  Its row values are `⊥`, `1` and `ω + 2`, each row is a lawful
section, and bountifulness reduces to the two capped lifts above. -/
private theorem isLegal_fiveCellScheme : fiveCellScheme.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 5, fiveCells.scope d ∈ fiveCells.faces ∧ 0 < fiveCells.grade d ∧
        fiveCells.grade d ≤ #(fiveCells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 5, fiveCellRows.{u} s d = ⊥ ∨ fiveCellRows.{u} s d = 1 ∨
        fiveCellRows.{u} s d = omegaAddTwo := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [fiveCellRows]
    rw [fiveCellScheme_row]
    rcases key s t.1 with h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
  isConsistent s := by
    fin_cases s
    · have hl := isLawfulBelow_fiveCellScheme
        (w := ![omegaAddTwo, ⊥, omegaAddTwo, omegaAddTwo, ⊥])
        (isLawful_fiveCellScheme rfl rfl isSelfVisible_omegaAddTwo isSelfVisible_omegaAddTwo
          isSelfVisible_omegaAddTwo le_rfl le_rfl le_sup_left) (fiveCells.gradedIndex 0)
      have hrow : fiveCellScheme.{u}.rows.row 0 =
          fun d ↦ (![omegaAddTwo, ⊥, omegaAddTwo, omegaAddTwo, ⊥] : Fin 5 → Label.{u}) d.1 := by
        funext ⟨d, hd⟩
        have key : ∀ d : Fin 5, fiveCells.gradedIndex d ≤ fiveCells.gradedIndex 0 → d = 0 := by
          decide
        obtain rfl := key d hd
        rfl
      -- consistency of the row at `0` is its lawfulness below the graded index of `0`
      change fiveCellScheme.{u}.rows.IsLawfulBelow (fiveCells.gradedIndex 0)
        (fiveCellScheme.{u}.rows.row 0)
      rw [hrow]
      exact hl
    · exact CellScheme.Rows.isLawfulBelow_const_bot _
    · exact isLawfulBelow_fiveCellScheme (w := fiveCellRows 2)
        (isLawful_fiveCellScheme rfl rfl isSelfVisible_omegaAddTwo isSelfVisible_omegaAddTwo
          (isSelfVisible_one.mpr le_rfl) le_rfl one_le_omegaAddTwo le_sup_left) _
    · exact isLawfulBelow_fiveCellScheme (w := fiveCellRows 3)
        (isLawful_fiveCellScheme rfl rfl isSelfVisible_omegaAddTwo (isSelfVisible_one.mpr le_rfl)
          isSelfVisible_omegaAddTwo one_le_omegaAddTwo le_rfl le_sup_right) _
    · exact CellScheme.Rows.isLawfulBelow_const_bot _
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨-, hj0, hjB⟩ := hX
    obtain ⟨hBC, -⟩ := h
    have key : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ ∅ →
        B = C ∨ (B = {0} ∧ C = Finset.univ) ∨ (B = {1} ∧ C = Finset.univ) := by decide
    have hB : B ≠ ∅ := by
      rintro rfl
      simp at hjB
      omega
    rcases key B C hBC hB with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_scope_zero _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_scope_one _
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨-, hj0, hjB⟩ := hX
    have hj2 : j ≤ 2 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 2), ∀ j : Fin 3, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
        ∃ d : Fin 5, fiveCells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B ⟨j, by omega⟩ hj0 hjB

/-! ### Two lifts with the twins in both orders -/

/-- The label `β + n`. -/
private noncomputable abbrev labelAdd (β : Ordinal.{u}) (n : ℕ) : Label.{u} :=
  ((β + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

private theorem labelAdd_le (β : Ordinal.{u}) {n n' : ℕ} (h : n ≤ n') :
    labelAdd β n ≤ labelAdd β n' :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (add_le_add_right (Nat.cast_le.mpr h) β))

private theorem not_labelAdd_two_le_one {β : Ordinal.{u}} : ¬ labelAdd β 2 ≤ labelAdd β 1 :=
  fun h ↦ by
    have := Nat.cast_le.mp ((add_le_add_iff_left β).mp
      (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)))
    omega

private theorem labelAdd_lt (β : Ordinal.{u}) (n : ℕ) :
    labelAdd β n < ((β + ω : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (add_lt_add_right (natCast_lt_omega0 n) β))

/-- The first lift `(β + 2, ⊥, β + 2, β + 1, ⊥)`: the second twin below `0`. -/
private noncomputable def fiveCellLift₁ (β : Ordinal.{u}) : Fin 5 → Label.{u} :=
  ![labelAdd β 2, ⊥, labelAdd β 2, labelAdd β 1, ⊥]

/-- The second lift `(β + 2, ⊥, β + 1, β + 2, ⊥)`: the first twin below `0`. -/
private noncomputable def fiveCellLift₂ (β : Ordinal.{u}) : Fin 5 → Label.{u} :=
  ![labelAdd β 2, ⊥, labelAdd β 1, labelAdd β 2, ⊥]

private theorem isLawful_fiveCellLift₁ {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    fiveCellScheme.{u}.rows.IsLawful (fiveCellLift₁ β) :=
  isLawful_fiveCellScheme rfl rfl (isSelfVisible_coe_add hβ (by omega))
    (isSelfVisible_coe_add hβ (by omega)) (isSelfVisible_coe_add hβ (by omega)) le_rfl
    (labelAdd_le β (by omega)) le_sup_left

private theorem isLawful_fiveCellLift₂ {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    fiveCellScheme.{u}.rows.IsLawful (fiveCellLift₂ β) :=
  isLawful_fiveCellScheme rfl rfl (isSelfVisible_coe_add hβ (by omega))
    (isSelfVisible_coe_add hβ (by omega)) (isSelfVisible_coe_add hβ (by omega))
    (labelAdd_le β (by omega)) le_rfl le_sup_right

private theorem atStage_fiveCellLift₁ {β : Ordinal.{u}} (d : Fin 5) :
    AtStage (β + ω) (fiveCellLift₁ β d) := by
  fin_cases d <;> first | exact .inl (labelAdd_lt β _) | exact atStage_bot

private theorem atStage_fiveCellLift₂ {β : Ordinal.{u}} (d : Fin 5) :
    AtStage (β + ω) (fiveCellLift₂ β d) := by
  fin_cases d <;> first | exact .inl (labelAdd_lt β _) | exact atStage_bot

/-- The stage type at `β + ω` with the labels of the first lift. -/
private noncomputable def fiveCellLiftType {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    StageType.{u} (β + ω) 2 where
  toScheme := fiveCellScheme
  label := fiveCellLift₁ β
  isWellFormed := isLegal_fiveCellScheme.isWellFormed
  isCoded := isLegal_fiveCellScheme.isCoded
  isLawful := isLawful_fiveCellLift₁ hβ
  atStage := atStage_fiveCellLift₁

/-- Its reduction to `β`, labelled `(⊤, ⊥, ⊤, ⊤, ⊥)`: `0` and the twins are labelled the formal
top. -/
private noncomputable def fiveCellType {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    StageType.{u} β 2 :=
  (fiveCellLiftType hβ).reduce hβ

private theorem reduce_labelAdd {β : Ordinal.{u}} (n : ℕ) :
    Label.reduce β (labelAdd β n) = ⊤ :=
  Label.reduce_of_le (Label.coe_le_coe_add β n)

/-- **Twin ordering is false at every stage that is zero or a limit**: on the legal type
`fiveCellType`, with `s₀ = 0` and `t₀ = 2`, the cell given at the graded index of the twins is one
of them, and one of the two lifts puts it below `s₀`. -/
theorem not_twinOrdering {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    ¬ TwinOrdering.{u} β := fun h ↦ by
  have hred₂ : ∀ d, Label.reduce β (fiveCellLift₂ β d) = (fiveCellType hβ).label d := by
    intro d
    -- the labels of `fiveCellType` are the reductions of those of the first lift
    change Label.reduce β (fiveCellLift₂ β d) = Label.reduce β (fiveCellLift₁ β d)
    fin_cases d <;> simp [fiveCellLift₁, fiveCellLift₂]
  obtain ⟨w, hw, -, hle⟩ := h (fiveCellType hβ) ((isLegal_reduce_iff hβ).mpr isLegal_fiveCellScheme)
    (0 : Fin 5) (2 : Fin 5) (show fiveCells.scope 0 ⊂ fiveCells.scope 2 by decide) rfl
    (reduce_labelAdd 2) (reduce_labelAdd 2)
  have h₁ := hle (fiveCellLift₁ β) (isLawful_fiveCellLift₁ hβ) atStage_fiveCellLift₁ fun _ ↦ rfl
  have h₂ := hle (fiveCellLift₂ β) (isLawful_fiveCellLift₂ hβ) atStage_fiveCellLift₂ hred₂
  have key : ∀ u : Fin 5, fiveCells.gradedIndex u = fiveCells.gradedIndex 2 → u = 2 ∨ u = 3 := by
    decide
  rcases key w hw with rfl | rfl
  · exact not_labelAdd_two_le_one h₂
  · exact not_labelAdd_two_le_one h₁

/-- **Twin ordering is false at every block stage.** -/
theorem not_twinOrdering_blockStage (ξ : Ordinal.{u}) : ¬ TwinOrdering.{u} (blockStage ξ) :=
  not_twinOrdering (isSuccPrelimit_blockStage ξ)

/-- No model at a block stage comes with twin ordering. -/
example {M : Type v} {ξ : Ordinal.{u}} (R : Realization.{u, v} (blockStage ξ) M) :
    ¬ (R.IsModel ∧ TwinOrdering.{u} (blockStage ξ)) :=
  fun h ↦ not_twinOrdering_blockStage ξ h.2

end VaughtConjecture.Continuation.CandidateCounterexamples

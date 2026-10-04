/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate
import VaughtConjecture.Extension.SmallArityExamples

/-!
# Synchronizing cofaces are refuted

Negative special cases for availability of the stable section at twins
(`VaughtConjecture.Continuation.Candidate`).  **Synchronizing cofaces** at a stage `β` would
transfer forcing from a cell `a` to a cell `b` through one more point: for a legal stage type `q`
at `β` and cells `a`, `b` with the scope of `a` in that of `b` and equal grades, some scheme `S` on
one more point carries a legal coface of `q`, and every lawful section of the rows of `S` is at
least as large at `b` as at `a`.  Three forms are refuted here, each defined in this file only:

* **unrestricted** (`UnrestrictedSynchronizingCofaces`, no requirement on the labels of `a` and
  `b`), false at `ω` (`not_unrestrictedSynchronizingCofaces`): the labels of a member of the coface
  family are a lawful section of `S` extending those of `q`, so the statement forces
  `q.label a ≤ q.label b`, and the legal stage type with labels `(⊥, 1)` at two cells of one graded
  index of `SmallArityExamples.onePointScheme 2` refutes it;
* **at cells labelled the formal top** (`SynchronizingCofaces`), false at every stage `β ≥ ω`,
  in particular at every block stage (`not_synchronizingCofaces_blockStage`): by bountifulness of
  the scheme of a legal coface (cap `⊥`), every lawful section of the rows of `q` extends to a
  lawful section of `S`, so the statement forces `ℓ a ≤ ℓ b` for every such `ℓ`; the reduction to
  `β` of the stage type at `ω + ω` with labels `(ω + 1, ω + 2)` on the same scheme has both cells
  labelled the formal top, and its lift `(ω + 1, ω + 2)` refutes it;
* **on lifts** (`SynchronizingCofacesOnLifts`, only the lawful sections of `S` at `β + ω` that lift
  a member of the coface family), false at `ω` (`not_synchronizingCofacesOnLifts`): extend the
  same lift to `S`, collapse it above `ω + 3`, and reduce it to a member of the family.

In each case the two cells share a graded index, so the counterexample is a pair of twins.  The
coface that adds one cell of the grade of `a`, alone at its graded index, with a tie from its row
to `b`, is in particular not legal on these stage types.  Whether stable availability holds for
twin types in models is open; `TwinOrdering` is the open hypothesis under which it is proved.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Continuation.CandidateCounterexamples

open Finset Ordinal StageType CellScheme Label SmallArityExamples

/-! ### Three forms of synchronizing cofaces -/

/-- **Unrestricted synchronizing cofaces** at `β`, with no requirement on the labels of the two
cells.  Refuted at `ω` (`not_unrestrictedSynchronizingCofaces`). -/
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
  · change IsSelfVisible 1 (1 : Label.{0})
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

/-- **Unrestricted synchronizing cofaces are false at `ω`**: they would give `1 ≤ ⊥`. -/
theorem not_unrestrictedSynchronizingCofaces : ¬ UnrestrictedSynchronizingCofaces.{0} ω :=
  fun h ↦ by
    have := label_le_of_unrestrictedSynchronizingCofaces h typeBotOne isLegal_botOne
      ⟨1, by decide⟩ ⟨0, by decide⟩ subset_rfl rfl
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

end VaughtConjecture.Continuation.CandidateCounterexamples

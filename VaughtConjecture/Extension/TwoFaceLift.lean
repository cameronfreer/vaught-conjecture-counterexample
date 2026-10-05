/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Tower

/-!
# The two-face lift at the grade one, and the completion below the full grade at arity at most two

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here the two-face lift
`2FL(1)` and the completion at the arities `m ≤ 2`); semantic contract, items 2–4.

Let `I` be a seed on `m + 2` points, with coatoms `C = univ.erase (Fin.last (m + 1))` and
`D = univ.erase (Fin.castSucc (Fin.last m))`, and tower `T j` (module
`VaughtConjecture.Extension.Tower`).

**`2FL(1)` holds at every arity** (`Seed.twoFaceLift_one`).  Fix a catalogue entry `a` of the layer
at the grade `2`, a cap `γ` with `⊥ < γ`, self-visible and short at `2` (shortness is not used),
and a labelling `w` of the amalgam lawful below `(C, 2)` and `(D, 2)` that agrees with `a` capped
at `γ` on the old cells of grade at most `2`.  Write `q` for `a` below `(univ, 1)`.  If `q < γ`
everywhere, then `q` itself is the extension.  Otherwise:

1. **The serving cell.**  By availability some new cell `u` of graded index `(univ, 1)` has
   `γ ≤ q u`; we call it a *serving cell*.  Its row `S` below `(univ, 1)` is lawful, never `⊤`, and
   self-visible at `1`, every cell there having grade `1`.  A witness `τ` bounded by the grade `1`
   carries `S` to `q` capped at `γ` (`CellScheme.Rows.exists_isWitness_rowBelow`), at every cell
   below `(univ, 1)`, old and new.
2. **The source cap, without an owner.**  Call a cell `e` below `(univ, 1)` *saturated* when
   `τ (S e) = γ`; the serving cell is saturated.  The source cap `h₁` is the least value of `S` on
   the saturated cells.  An old cell where `w` exceeds `γ` is saturated, so `S` is at least `h₁`
   there: the alignment of the prescription with the source is in the first case of the owner
   alignment (`Label.exists_ownerAlignment`) **automatically, because every value of a row of the
   layer at the grade `1` is self-visible at `1`**.  No owner of the prescription is used.
3. **The two-face aligned encoding.**  The prescription `w`, read on the old cells, is
   aligned-encoded at the source cap `h₁` relative to `S` (`Label.alignedEncode`), lawfully below
   `(C, 1)` and below `(D, 1)` separately (`CellScheme.Rows.IsLawfulBelow.alignedEncode`): the
   encoding is a pointwise formula, lawful wherever its source and prescription are.
4. **The extension through the layer at the grade `1`** along the row of the serving cell
   (`Scheme.extendsFromBoundary_fieldLayer` at the grade `1`, where the canonical code has
   relative room at every positive self-visible cap).
5. **Decoding** by the aligned decoder (`Label.alignedDecode`), a witness bounded by the grade `1`;
   the laws below `(univ, 1)` are carried with `q` as lawful companion
   (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).

The result agrees with `w` at the old cells of grade `1`, on both coatoms and above `γ` included,
and with `a` capped at `γ` everywhere.  Only lawfulness of `w` at the grade `1` below each coatom is
used; lawfulness at the grade `2` is used by the step itself, when it glues the extension with the
old cells of the grade `2` over `(C, 2)`, `(univ, 1)` and `(D, 2)`
(`CellScheme.Rows.IsLawfulBelow.glue₃` in `Seed.exists_isLawfulBelow_of_twoFaceLift`).

**The invariant and the completion at the arities `m ≤ 2`.**  At those arities `2FL(1)` is the
only instance the recursion assumes, so the lifting invariant holds up to the grade `m + 1`
(`Seed.towerInvariant_of_le_two`).  From the invariant at the top grade, the scheme `T (m + 1)` is
bountiful (`Seed.isBountiful_tower`: off the full face through the source prefix and the
bountifulness of the amalgam, from each coatom to the full face by the invariant) and legal below
the full grade (`Seed.isLegalBelowFullGrade_tower`), and with the labelling extended through the
tower it is a completion below the full grade (`Seed.completionBelowFullGradeOfTowerInvariant`).
So every seed with `m ≤ 2` has one (`Seed.nonempty_completionBelowFullGrade_of_le_two`), and at
every arity a seed has one when it satisfies `2FL(j)` at the grades `2 ≤ j < m`
(`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift`, a hypothesis on the seed).

**`2FL(j)` for `j ≥ 2` is not a property of every seed.**  The rows of the layer at a grade
`ℓ ≥ 2` read lower-grade values through their orbit codes, which are not self-visible at `ℓ`, and
the alignment of step 2 can then meet a *strip case*: two saturated cells, one on `C` and one on
`D`, with equal entry of the serving row just below the source cap `h₁` (in the strip of finite
parts below the grade) and with prescriptions that differ above `γ`.  In that case the extension
need not exist: `2FL(2)` fails for a legal seed on five points
(`TwoFaceLiftCounterexample.not_twoFaceLift_two`), so `2FL(j)` at the grades `2 ≤ j < m` is false
as a statement about every seed, at every stage
(`TwoFaceLiftCounterexample.not_forall_twoFaceLift`).  This is a non-existence, not a limitation
of an encoding: for that seed, for some catalogue entry `a`, cap `h` and prescription `w`, no
labelling with the properties of `2FL(2)` exists.  The completion below the full grade of that
seed exists nevertheless (`TwoFaceLiftCounterexample.nonempty_completionBelowFullGrade_seed4`),
through the step from deadness of the old cells of the grade `3`: they are *dead*, that is, `⊥` in
every labelling of the amalgam lawful below a coatom (`Seed.DeadAt 2`;
`Seed.towerInvariant_succ_of_dead`, module `VaughtConjecture.Extension.DeadCellStep`).

**The step, stated exactly, and what stays open.**  Neither boundary triple of the library for the
step to a grade `j + 1 ≤ m` serves every seed: the triple through `(D, j + 1)` uses `2FL(j)`, which
fails for a legal seed at `j = 2`; the triple through `(univ, j)` uses a union fill of the other
coatom over the common face, which fails for a legal seed at the grade `2` (module
`VaughtConjecture.Extension.UnionFillCounterexample`).  Each serves some seeds: the first at `j = 1`
(`Seed.twoFaceLift_one`), the second when the old cells of the grade `j + 1` are dead
(`Seed.towerInvariant_succ_of_dead`) and at the top grade (`Seed.towerInvariant_top`).  The case
split `2FL(j) ∨ Seed.DeadAt j` does not cover every legal seed either: both fail at `j = 2` for a
legal seed on five points
(`CaseSplitCounterexample.not_forall_twoFaceLift_or_deadAt`), which nevertheless has a
completion below the full grade.  The hypothesis of the step, stated exactly, is the *existential
two-face lift* `2FL∃(j)` (`Seed.TwoFaceLiftExists`, module
`VaughtConjecture.Extension.TwoFaceLiftExists`): for every catalogue entry `a` at the grade
`j + 1`, every cap `h` self-visible and short at `j + 1` with `⊥ < h`, and every labelling `w_C`
lawful below `(C, j + 1)` that agrees with `a` capped at `h`, the step chooses a labelling `w_D`
lawful below `(D, j + 1)`, equal to `w_C` at the cells of the common face of grade at most `j + 1`
and agreeing with `a` capped at `h`, such that the labelling glued from `w_C` and `w_D` satisfies
the conclusion of `2FL(j)`.  For `j ≤ m` and under the invariant at the grade `j`, the invariant at
`j + 1` holds exactly when `2FL∃(j)` does (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`), and
the invariant at the top grade holds exactly when `2FL∃(j)` holds at the grades `2 ≤ j < m`
(`Seed.towerInvariant_top_iff`): a reformulation of the step through the tower, not a weaker
sufficient hypothesis.  The step uses `CellScheme.Rows.cappedLift_of_boundaries_short` with the
degenerate triple `U = V = O = (C, j + 1)` at the positive caps; the choice of `w_D` is made inside
the hypothesis.  `2FL∃(j)` holds under `2FL(j)` (for `j ≤ m`), under deadness together with the
invariant at `j`, and for the seeds whose two coatom types are the type `T5` of the module
`VaughtConjecture.Extension.CaseSplitCounterexample`, where neither `2FL(2)` nor deadness
holds; for the seed of the failure of `2FL(2)` above it holds by deadness
(`CaseSplitCounterexample.twoFaceLiftExists_two_seed4`).

The step fails for a legal seed.  For the seed `seedL` on five points whose two coatom types differ
and share a face, with a row coupling the cell of the common face to cells of lower grade on one
side only, `2FL∃(2)` fails
(`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`, module
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`): the strip case occurs together with
that coupling, and no choice of `w_D` gives the extension.  So the tower does not complete every
seed, and `2FL∃(j)` for every seed at the grades `2 ≤ j < m` is false at every stage
(`TwoFaceLiftExistsCounterexample.not_forall_twoFaceLiftExists`).  A redesign of the layers under
which a two-face lift at the grade `2` would hold for every seed is not pursued: the identified
obstruction survives the redesigns examined (of the encoding, of the alignment, of the catalogue
at the grade `2`, of the grid of agreement heights, and of an owner seeing both faces).  The coatom
extension properties `StageType.HasApexCoatomExtensions` and `StageType.HasCoatomExtensions` at
the stages that are zero or a limit quantify over the seeds of every arity
(`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`); they remain to be proved, and
they are not refuted, nor is a completion below the full grade of `seedL` by another
construction.  Whether `seedL` has a completion below the full grade at all is open.

No hypothesis on the stage enters, no union fill (module
`VaughtConjecture.Extension.UnionFillCounterexample`) and no completion is assumed, and neither
`CompletionBelowFullGrade.cappedLift_of_ne_univ` nor `CompletionBelowFullGrade.isSourcePrefix`
is used in building the completion.

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-! ### The two-face lift at the grade one -/

/-- The rows of the new cells of the layer at the grade `1` are never `⊤`. -/
private theorem rowBelow_ne_top_one {u : Fin (I.tower 1).card}
    (hu : (I.tower 1).toCellScheme.gradedIndex u = (univ, 1))
    (d : (I.tower 1).toCellScheme.below (univ, 1)) :
    (I.tower 1).rows.rowBelow u hu d ≠ ⊤ := by
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower 0) (k := 1)
    (hS := I.not_univ_succ_le_tower 0) hu
  exact (Scheme.isShort_ne_top_row_fieldLayer (hS := I.not_univ_succ_le_tower 0) i _).2

/-- **The two-face lift `2FL(1)` holds at every arity.**  Along every catalogue entry `a` of the
layer at the grade `2`, at every cap `γ` self-visible and short at `2` with `⊥ < γ`, a labelling `w`
of the amalgam lawful below both coatoms at the grade `2` and agreeing with `a` capped at `γ`
extends through the layer at the grade `1`, unchanged at the old cells of grade `1`, to a labelling
lawful below `(univ, 1)` agreeing with `a` capped at `γ`.

The proof (module docstring, steps 1–5): a serving cell `u` of the layer at the grade `1`, where
`a` reaches the cap; a witness `τ` bounded by the grade `1` from the row `S` of `u` to `a` capped at
`γ`; the source cap `h₁`, least value of `S` on the saturated cells, which is automatically aligned
with `w` since every value of `S` is self-visible at `1`; the aligned encoding of `w` relative to
`S` at `h₁`, lawful below each coatom at the grade `1`; its extension through the layer along `S`;
and the aligned decoding.  Shortness of `γ` is not used, only `IsSelfVisible 1 γ` and `⊥ < γ`;
neither is lawfulness of `w` at the grade `2`. -/
theorem twoFaceLift_one : I.TwoFaceLift 1 := by
  classical
  intro a ha γ hγ _hγs hγbot w hwx hwy hag
  have hγ1 : IsSelfVisible 1 γ := hγ.mono (by omega)
  have haL : (I.tower 1).rows.IsLawful a := (Scheme.mem_catalogue.mp ha).1
  set q : (I.tower 1).toCellScheme.below (univ, 1) → Label.{u} := fun e ↦ a e with hq_def
  have hq : (I.tower 1).rows.IsLawfulBelow (univ, 1) q := haL.isLawfulBelow _
  have hwf := (I.isWellFormed_tower 1 (by omega)).isWellFormed
  have hgr1 (e : Fin (I.tower 1).card) (he : e ∈ (I.tower 1).toCellScheme.below (univ, 1)) :
      (I.tower 1).toCellScheme.grade e = 1 := le_antisymm he.2 (hwf.grade_pos e)
  have hag1 (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      min (w d) γ = min (a (I.towerEmbed 1 d)) γ := hag d (by omega)
  by_cases hsat : ∃ e : (I.tower 1).toCellScheme.below (univ, 1), γ ≤ q e
  swap
  · -- The ambient stays below the cap: it is its own extension.
    push Not at hsat
    refine ⟨q, hq, fun d hd ↦ ?_, fun e ↦ rfl⟩
    have hlt : a (I.towerEmbed 1 d) < γ := hsat ⟨I.towerEmbed 1 d, I.towerEmbed_mem_below hd⟩
    have h1 := hag1 d hd
    rw [min_eq_left hlt.le] at h1
    have hwd : w d < γ := by
      by_contra hc
      rw [min_eq_right (not_lt.mp hc)] at h1
      exact hlt.ne h1.symm
    rw [min_eq_left hwd.le] at h1
    exact h1.symm
  obtain ⟨d₀, hd₀⟩ := hsat
  -- The serving cell: a new cell of the layer where the ambient reaches the cap.
  obtain ⟨t, ht⟩ : ∃ t, (I.tower 1).toCellScheme.gradedIndex t = (univ, 1) :=
    I.exists_gradedIndex_eq_univ_tower 0
  obtain ⟨u, hu, hle⟩ := (Rows.isLawfulBelow_iff_forall.mp
    (Rows.isLawfulBelow_extendBot.mpr hq)).2.2 d₀.1 t ht.le
    (d₀.2.1.trans (congrArg Prod.fst ht).ge) ((hgr1 _ d₀.2).trans (congrArg Prod.snd ht).symm)
  have hu' : (I.tower 1).toCellScheme.gradedIndex u = (univ, 1) := hu.trans ht
  rw [Rows.extendBot_of_mem q d₀.2, Rows.extendBot_of_mem q hu'.le] at hle
  obtain ⟨τ, hτ, -, hτS⟩ := Rows.exists_isWitness_rowBelow hu' hq hγ1 (hd₀.trans hle)
  set S := (I.tower 1).rows.rowBelow u hu' with hS_def
  have hSlaw : (I.tower 1).rows.IsLawfulBelow (univ, 1) S :=
    Rows.isLawfulBelow_rowBelow hu' (I.isConsistent_tower 1 u)
  have hSvis (e : (I.tower 1).toCellScheme.below (univ, 1)) : IsSelfVisible 1 (S e) := by
    have h' := (Rows.isLawfulBelow_iff_forall.mp (Rows.isLawfulBelow_extendBot.mpr hSlaw)).1
      e.1 e.2
    rwa [hgr1 _ e.2, Rows.extendBot_of_mem S e.2] at h'
  -- The source cap: the least source value over the saturated cells.
  set sat := (Finset.univ : Finset ((I.tower 1).toCellScheme.below (univ, 1))).filter
    (fun e ↦ τ (S e) = γ) with hsat_def
  have hu_mem : (⟨u, hu'.le⟩ : (I.tower 1).toCellScheme.below (univ, 1)) ∈ sat := by
    rw [hsat_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hS_def, hτS]
    exact min_eq_right (hd₀.trans hle)
  obtain ⟨e₀, he₀, hmin⟩ := sat.exists_min_image S ⟨_, hu_mem⟩
  set h₁ := S e₀ with hh₁_def
  have hτh : τ h₁ = γ := (Finset.mem_filter.mp he₀).2
  have hhbot : ⊥ < h₁ := bot_lt_iff_ne_bot.mpr fun hb ↦ by
    rw [hb, hτ.map_bot] at hτh
    exact hγbot.ne hτh
  have hhvis : IsSelfVisible 1 h₁ := hSvis e₀
  obtain ⟨μ, hμ, hhμ⟩ := exists_isSuccPrelimit_lt (I.rowBelow_ne_top_one hu' e₀)
  -- The source and the prescription on all cells.
  set S' : Fin (I.tower 1).card → Label.{u} := Rows.extendBot (univ, 1) S with hS'_def
  set P : Fin (I.tower 1).card → Label.{u} :=
    Function.extend (I.towerEmbed 1) w (fun _ ↦ ⊥) with hP_def
  have hP (d : Fin I.amalgam.card) : P (I.towerEmbed 1 d) = w d :=
    (I.towerEmbed 1).injective.extend_apply _ _ _
  set V : Finset Label.{u} := Finset.univ.image w with hV_def
  set f : Fin (I.tower 1).card → Label.{u} := Label.alignedEncode μ V 1 h₁ γ S' P with hf_def
  -- At an old cell of grade one, the source decodes to the prescription capped at `γ`.
  have hτold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      τ (S' (I.towerEmbed 1 d)) = min (w d) γ := by
    rw [hS'_def, Rows.extendBot_of_mem S (I.towerEmbed_mem_below hd), hS_def, hτS, hag1 d hd]
  -- The cells below either coatom at the grade one are old.
  have hold (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1)) :
      ∃ d, ∃ hd : I.amalgam.toCellScheme.grade d ≤ 1, I.towerEmbed 1 d = e := by
    have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hsu ↦ he.elim
      (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hsu.ge.trans h'.1)))
      fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hsu.ge.trans h'.1))
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
    refine ⟨d, ?_, rfl⟩
    have h2 : (I.tower 1).toCellScheme.grade (I.towerEmbed 1 d) ≤ 1 := he.elim (·.2) (·.2)
    rwa [grade_towerEmbed] at h2
  -- The alignment: a prescription above the cap sits on a saturated cell.
  have halign (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1))
      (hpe : γ < P e) : h₁ ≤ S' e := by
    obtain ⟨d, hd, rfl⟩ := hold e he
    rw [hP] at hpe
    have hsd : τ (S' (I.towerEmbed 1 d)) = γ := by rw [hτold d hd, min_eq_right hpe.le]
    have hmem := I.towerEmbed_mem_below hd
    rw [hS'_def, Rows.extendBot_of_mem S hmem] at hsd ⊢
    exact hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsd⟩)
  -- The aligned encoding is lawful below each coatom at the grade one.
  have hS'law : (I.tower 1).rows.IsLawfulBelow (univ, 1) fun e ↦ S' e :=
    Rows.isLawfulBelow_extendBot.mpr hSlaw
  have hfX (x : Fin (m + 2))
      (hwX : I.amalgam.rows.IsLawfulBelow (univ.erase x, 1 + 1) fun d ↦ w d)
      (hcov : ∀ e, e ∈ (I.tower 1).toCellScheme.below (univ.erase x, 1) →
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
          e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1)) :
      (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ f e := by
    have hsX : (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ S' e :=
      hS'law.mono (X := (univ.erase x, 1)) ⟨subset_univ _, le_rfl⟩
    have hpX : (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ P e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
      simp only [hP]
      exact hwX.mono (X := (univ.erase x, 1)) ⟨subset_rfl, by omega⟩
    exact Rows.IsLawfulBelow.alignedEncode (V := V) hsX hpX (fun d ↦ d.2.2) hhvis hhbot.ne' hγ1
      hμ hhμ fun e hpe ↦ halign e (hcov e e.2) hpe
  have hfC := hfX (Fin.last (m + 1)) hwx fun e he ↦ .inl he
  have hfD := hfX (Fin.castSucc (Fin.last m)) hwy fun e he ↦ .inr he
  -- The extension through the layer at the grade one along the row of the serving cell.
  have hnot (z : Fin (m + 2)) : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ (univ.erase z, 1) :=
    fun h ↦ ne_univ_erase z (univ_subset_iff.mp h.1)
  have hcover (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.last (m + 1)), 1) ∨
        I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.castSucc (Fin.last m)), 1) :=
    (I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun h ↦ ⟨h, hd⟩) fun h ↦ ⟨h, hd⟩
  have hpos (d : Fin I.amalgam.card) : 1 ≤ I.amalgam.toCellScheme.grade d :=
    (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).2.1
  have hext : (I.tower 1).rows.ExtendsFromBoundary (univ.erase (Fin.last (m + 1)), 1)
      (univ.erase (Fin.castSucc (Fin.last m)), 1) (univ, 1) h₁ S :=
    Scheme.extendsFromBoundary_fieldLayer (S := I.tower 0) (k := 1)
      (hS := I.not_univ_succ_le_tower 0) (fun d hd ↦ le_antisymm hd (hpos d)) (hnot _) (hnot _)
      hcover hu' hhvis hhbot
  obtain ⟨r', hr', hr'f, hr'S⟩ := hext f hfC hfD fun d hd ↦ by
    rw [hf_def, min_alignedEncode hhμ (halign d.1 hd), hS'_def, Rows.extendBot_of_mem S d.2]
  -- Decoding.
  set ρ := alignedDecode μ V 1 τ γ with hρ_def
  have hρ : IsWitness (stepSuppressor.{u} 1) ρ := isWitness_alignedDecode hμ hτ hγ1
  have hamb (d : (I.tower 1).toCellScheme.below (univ, 1)) : min (ρ (r' d)) γ = min (q d) γ := by
    rw [hρ_def, min_alignedDecode_eq hτ.monotone le_rfl hτh.ge hhμ (hr'S d), hS_def, hτS d,
      min_assoc, min_self]
  refine ⟨ρ ∘ r', hr'.map_of_min_eq hq (fun d ↦ d.2.2) hρ hγbot.ne' hamb, fun d hd ↦ ?_, hamb⟩
  have hb : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
      I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last m)), 1) :=
    (I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
      fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩
  rw [Function.comp_apply, hr'f _ hb, hf_def, hρ_def]
  rw [alignedDecode_alignedEncode hτ.monotone hhμ hτh.ge ?_ ?_, hP]
  · rw [hτold d hd, hP, min_assoc, min_self]
  · intro _
    rw [hP]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

/-- **The two-face lift at the grades below `m`, from the grade `2` on**: together with `2FL(1)`,
`2FL(j)` at the grades `2 ≤ j < m` is the hypothesis of `Seed.towerInvariant_of_twoFaceLift`. -/
theorem forall_twoFaceLift_of_two_le (h2 : ∀ j, 2 ≤ j → j < m → I.TwoFaceLift j) :
    ∀ j, 1 ≤ j → j < m → I.TwoFaceLift j := fun j hj hjm ↦
  if hj1 : j = 1 then hj1 ▸ I.twoFaceLift_one else h2 j (by omega) hjm

/-- **The invariant up to the grade `m + 1` at the arities `m ≤ 2`**, with no hypothesis: the
recursion `Seed.towerInvariant_of_twoFaceLift` assumes `2FL(j)` at the grades `1 ≤ j < m`, which
at `m ≤ 2` is at most `2FL(1)` (`Seed.twoFaceLift_one`). -/
theorem towerInvariant_of_le_two (hm : m ≤ 2) : ∀ j ≤ m + 1, I.TowerInvariant j :=
  I.towerInvariant_of_twoFaceLift
    (I.forall_twoFaceLift_of_two_le fun j hj hjm ↦ absurd hjm (by omega))

/-! ### The completion below the full grade from the invariant at the top grade -/

/-- **A cell at `(univ, j)` survives in every later scheme of the tower**: the cell of the layer
at the grade `j`, carried along `Fin.castAdd`. -/
theorem exists_gradedIndex_eq_univ_tower_of_le {j : ℕ} (hj : 1 ≤ j) :
    ∀ k, j ≤ k → ∃ t, (I.tower k).toCellScheme.gradedIndex t = (univ, j)
  | k, hk => by
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact I.exists_gradedIndex_eq_univ_tower i
    | succ k _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨Fin.castAdd ((I.tower k).catalogue (k + 1)).card t,
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ t).trans ht⟩

/-- **The graded faces of the tower are those of the amalgam**, its faces being those of the
amalgam (`Seed.faces_tower`). -/
theorem gradedFaces_tower (j : ℕ) :
    (I.tower j).toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
  ext X
  simp only [CellScheme.mem_gradedFaces, I.faces_tower j]

/-- **Bountifulness of the tower at the top grade, from the invariant**
(`CellScheme.Rows.isBountiful_of_coatoms`): a lift between graded faces not reaching the full face
is a lift of the amalgam, through the source prefix (`Seed.cappedLift_tower_iff`) and the
bountifulness of the amalgam; the lifts from each coatom to the full face are the invariant. -/
theorem isBountiful_tower (hinv : I.TowerInvariant (m + 1)) :
    (I.tower (m + 1)).rows.IsBountiful := by
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]; rfl
  refine Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last (m + 1))
    (b := Fin.castSucc (Fin.last m)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (I.faces_tower (m + 1) ▸ hB) hne)
    (I.faces_tower (m + 1) ▸ I.erase_last_mem_faces)
    (I.faces_tower (m + 1) ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY h hYne ↦ (I.cappedLift_tower_iff h hYne).mpr
      (I.isBountiful (I.gradedFaces_tower (m + 1) ▸ hX) (I.gradedFaces_tower (m + 1) ▸ hY) h))
    (fun j hj ↦ hinv _ (by simp) j (by rw [hcard] at hj; exact hj))
    fun j hj ↦ hinv _ (by simp) j (by rw [hcard] at hj; exact hj)

/-- **Legality of the tower below the full grade, from the invariant at the top grade**: the
structural laws of the tower, bountifulness (`Seed.isBountiful_tower`), and completeness: a graded
face of proper scope carries an old cell, and `(univ, j)` for `1 ≤ j ≤ m + 1` the cell of the
layer at the grade `j`. -/
theorem isLegalBelowFullGrade_tower (hinv : I.TowerInvariant (m + 1)) :
    (I.tower (m + 1)).IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_tower (m + 1) (by omega)
  isCoded := I.isCoded_tower (m + 1)
  isConsistent := I.isConsistent_tower (m + 1)
  isBountiful := I.isBountiful_tower hinv
  grade_lt d := I.grade_tower_lt le_rfl d
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨B, j⟩ := X
    by_cases hB : B = univ
    · subst hB
      exact I.exists_gradedIndex_eq_univ_tower_of_le hX.2.1 (m + 1) (by simp only at hX2; omega)
    · exact I.exists_gradedIndex_eq_tower (m + 1) (I.gradedFaces_tower (m + 1) ▸ hX) hB

/-- **The completion below the full grade, from the invariant at the top grade**: the scheme
`T (m + 1)` of the tower, with the old cells along `Seed.towerEmbed`, legal below the full grade
(`Seed.isLegalBelowFullGrade_tower`), and the glued labelling extended through the tower, every
old label kept literally (`Seed.exists_isLawful_tower`). -/
noncomputable def completionBelowFullGradeOfTowerInvariant (hinv : I.TowerInvariant (m + 1)) :
    CompletionBelowFullGrade I where
  scheme := I.tower (m + 1)
  embed := I.towerEmbed (m + 1)
  isLowerEmbedding := I.isLowerEmbedding_tower (m + 1)
  scope_embed := I.scope_towerEmbed (m + 1)
  comap_rows := I.comap_rows_tower (m + 1)
  mem_range_embed := I.mem_range_towerEmbed (m + 1)
  faces_eq := I.faces_tower (m + 1)
  isLegalBelowFullGrade := I.isLegalBelowFullGrade_tower hinv
  label := (I.exists_isLawful_tower (m + 1) I.amalgam.isLawful).choose
  isLawful := (I.exists_isLawful_tower (m + 1) I.amalgam.isLawful).choose_spec.1
  label_embed := (I.exists_isLawful_tower (m + 1) I.amalgam.isLawful).choose_spec.2

/-- **The completion below the full grade of a seed satisfying `2FL(j)` at the grades
`2 ≤ j < m`**, at every arity: `2FL(1)` holds (`Seed.twoFaceLift_one`), so the invariant holds up
to the top grade.  The hypothesis is on the seed `I`: it holds for every seed with `m ≤ 2`, and its
universal form over all seeds is refuted (`TwoFaceLiftCounterexample.not_forall_twoFaceLift`).  A
seed may instead have dead old cells at some of those grades
(`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`). -/
theorem nonempty_completionBelowFullGrade_of_twoFaceLift
    (h2 : ∀ j, 2 ≤ j → j < m → I.TwoFaceLift j) : Nonempty (CompletionBelowFullGrade I) :=
  ⟨I.completionBelowFullGradeOfTowerInvariant
    (I.towerInvariant_of_twoFaceLift (I.forall_twoFaceLift_of_two_le h2) (m + 1) le_rfl)⟩

/-- **Every seed with `m ≤ 2` has a completion below the full grade**, through the tower, with no
hypothesis: no grade `2 ≤ j < m` exists. -/
theorem nonempty_completionBelowFullGrade_of_le_two (hm : m ≤ 2) :
    Nonempty (CompletionBelowFullGrade I) :=
  I.nonempty_completionBelowFullGrade_of_twoFaceLift fun j hj hjm ↦ absurd hjm (by omega)

end VaughtConjecture.Seed

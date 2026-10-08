/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Witness
import VaughtConjecture.Extension.SmallArityExamples

/-!
# The low truncation at the root blocks (work file for `h3`)

Work file (placement later), for the weakened lower bound at the root (`H3.RootLowBound'`) of
`VaughtConjecture.MainTheorem.H3Witness`.  Compiled in this repository (theorem named):

* **The low cut** (`H3.lowCut_mono`, `H3.lowCut_eq_bot_of_le`, `H3.lowCut_min`): the low cut at the
  root blocks is monotone, `⊥` below a label that is `⊥` or low, and commutes with the cap at a
  label that is not low.
* **The low truncation is lawful when the rows separate the low labels by blocks**
  (`H3.isLawful_lowTruncation`, from `H3.LowBlockSeparated`, a named condition on `d`): for every
  cell `s` of `d` not `⊥` and not low, a cell `e` read by the row of `s` in the block of a cell `w`
  with a low label, at or above it, has a label `⊥` or low.  The witness of the truncated locality
  at `s` interpolates the capped witness of the locality of `d.label` at `s`, `⊥` on the blocks of
  the low reads (`Label.exists_isWitness_interpolation`).
* **The weakened lower bound at the root from the separation**
  (`H3.rootLowBound'_of_lowBlockSeparated`).
* **The converse** (`H3.lowBlockSeparated_of_isLawful_lowTruncation`, so
  `H3.isLawful_lowTruncation_iff`): at a failure of the separation the zero set of a witness of
  the truncated locality contains the block of the low read, so the truncation is not lawful.
  The second clause of `H3.RootLowBound'` is exactly the separation.
* **Legality does not bound the row offsets by the grade** (`H3.exists_isLegal_rowOffset_gt_grade`:
  a legal one-point scheme whose row reads its cell of grade `1` at `5`).
* **A witness matching a small prescription is `⊥` below its block**
  (`H3.witness_eq_bot_below_block`): every witness image of `d.label` matching the prescription at
  a cap at least `n + 1`, at a root cell where the prescription is below `n + 1`, is `⊥` below the
  block of that root cell; so the witness route needs a lawful labelling of `d` that is `⊥` at the
  cells labelled there.
* **The separation when the row offsets are at most the grade**
  (`H3.lowBlockSeparated_of_rowOffsets`): a read in the block of a low read and above it is a
  replacement of it at the grade of `s`, and the capped witness commutes with the replacements
  there.  So the separation can fail at `s` only at a read whose finite part exceeds the grade of
  `s`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace H3

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n}

/-- A label below one below the root blocks is below the root blocks. -/
theorem BelowRootBlocks.mono {y y' : Label.{u}} (h : BelowRootBlocks t y) (hle : y' ≤ y) :
    BelowRootBlocks t y' :=
  fun x μ i hμ hx ↦ hle.trans_lt (h x μ i hμ hx)

/-- The low cut at a label that is not low is the label. -/
theorem lowCut_of_not {y : Label.{u}} (h : ¬ (y ≠ ⊤ ∧ BelowRootBlocks t y)) : lowCut t y = y := by
  unfold lowCut
  split_ifs
  rfl

/-- The low cut at a low label is `⊥`. -/
theorem lowCut_of_low {y : Label.{u}} (h : y ≠ ⊤ ∧ BelowRootBlocks t y) : lowCut t y = ⊥ := by
  unfold lowCut
  split_ifs
  rfl

/-- The low cut is `⊥` at a label below one that is `⊥` or low. -/
theorem lowCut_eq_bot_of_le {y y' : Label.{u}} (hle : y' ≤ y)
    (h : y = ⊥ ∨ (y ≠ ⊤ ∧ BelowRootBlocks t y)) : lowCut t y' = ⊥ := by
  rcases h with h | ⟨hnt, hb⟩
  · rw [h, le_bot_iff] at hle
    rw [hle]
    unfold lowCut
    split_ifs <;> rfl
  · exact lowCut_of_low ⟨ne_top_of_le_ne_top hnt hle, hb.mono hle⟩

/-- **The low cut is monotone.** -/
theorem lowCut_mono : Monotone (lowCut t) := by
  intro y y' hle
  by_cases h : y' ≠ ⊤ ∧ BelowRootBlocks t y'
  · rw [lowCut_eq_bot_of_le hle (.inr h)]
    exact bot_le
  · rw [lowCut_of_not h]
    by_cases h' : y ≠ ⊤ ∧ BelowRootBlocks t y
    · rw [lowCut_of_low h']
      exact bot_le
    · rw [lowCut_of_not h']
      exact hle

/-- **The low cut commutes with the cap at a label that is not low.** -/
theorem lowCut_min {x y : Label.{u}} (hy : ¬ (y ≠ ⊤ ∧ BelowRootBlocks t y)) :
    lowCut t (min x y) = min (lowCut t x) y := by
  by_cases hx : x ≠ ⊤ ∧ BelowRootBlocks t x
  · rw [lowCut_eq_bot_of_le (min_le_left x y) (.inr hx), lowCut_of_low hx, min_eq_left bot_le]
  · rw [lowCut_of_not hx]
    rcases min_choice x y with h | h <;> rw [h]
    · exact lowCut_of_not hx
    · exact lowCut_of_not hy

variable (t) in
/-- **The rows of `d` separate the low labels by blocks** (a named condition): for every cell `s`
of `d` whose label is neither `⊥` nor low (not `⊤` and below the root blocks), and cells `w`, `e`
below `s` with the label of `w` low and not `⊥`, if the row of `s` reads `e` at or above `w` and
in its block (below a replacement of the reading of `w`), then the label of `e` is `⊥` or low. -/
def LowBlockSeparated (d : StageType.{u} α (n + 1)) : Prop :=
  ∀ (s : Fin d.card) (w e : d.toCellScheme.below (d.toCellScheme.gradedIndex s)),
    d.label s ≠ ⊥ → ¬ (d.label s ≠ ⊤ ∧ BelowRootBlocks t (d.label s)) →
    d.label w.1 ≠ ⊥ → d.label w.1 ≠ ⊤ → BelowRootBlocks t (d.label w.1) →
    d.rows.row s w ≤ d.rows.row s e →
    (∃ N : ℕ, d.rows.row s e ≤ visibilityReplace N N (d.rows.row s w)) →
    d.label e.1 = ⊥ ∨ (d.label e.1 ≠ ⊤ ∧ BelowRootBlocks t (d.label e.1))

/-- **The low truncation is lawful when the rows separate the low labels by blocks.**  Order and
availability pass through the monotone low cut.  At a cell `s` whose label is `⊥` or low the
truncated locality is the bottom one; otherwise the low cut commutes with the cap at `s`, and the
witness is the interpolation of the capped witness `τ` of the locality of `d.label` at `s` that is
`⊥` on the zero set of `τ` and on the blocks of the low reads, by the separation. -/
theorem isLawful_lowTruncation {d : StageType.{u} α (n + 1)} (hsep : LowBlockSeparated t d) :
    d.rows.IsLawful (lowTruncation t d) := by
  classical
  have hd := d.isLawful
  refine ⟨fun z ↦ ?_, fun s ↦ ?_, fun s s' hss hg ↦ ?_⟩
  · -- order
    change IsSelfVisible _ (lowCut t (d.label z))
    by_cases h : d.label z ≠ ⊤ ∧ BelowRootBlocks t (d.label z)
    · rw [lowCut_of_low h]
      exact isSelfVisible_bot _
    · rw [lowCut_of_not h]
      exact hd.orderly z
  · -- locality
    change TransformsTo _ _ fun w : d.toCellScheme.below (d.toCellScheme.gradedIndex s) ↦
      min (lowCut t (d.label w.1)) (lowCut t (d.label s))
    by_cases hs : d.label s = ⊥ ∨ (d.label s ≠ ⊤ ∧ BelowRootBlocks t (d.label s))
    · rw [lowCut_eq_bot_of_le le_rfl hs]
      simpa only [min_bot_right] using TransformsTo.bot _ (d.rows.row s)
    have hs0 : d.label s ≠ ⊥ := fun h ↦ hs (.inl h)
    have hsl : ¬ (d.label s ≠ ⊤ ∧ BelowRootBlocks t (d.label s)) := fun h ↦ hs (.inr h)
    rw [lowCut_of_not hsl]
    set D := d.toCellScheme
    set c : D.below (D.gradedIndex s) := ⟨s, D.mem_below_gradedIndex s⟩
    obtain ⟨τ, hτ, -, hτE⟩ := (hd.locality s).exists_isWitness_capped
      (p := fun w : D.below (D.gradedIndex s) ↦ d.label w.1) (c := c) (fun w ↦ w.2.2)
      (hd.orderly s)
    set E := d.rows.row s
    -- the zero set: the zero set of `τ` and the blocks of the low reads
    set S : Set Label.{u} := {x | τ x = ⊥ ∨ ∃ w : D.below (D.gradedIndex s), d.label w.1 ≠ ⊥ ∧
      d.label w.1 ≠ ⊤ ∧ BelowRootBlocks t (d.label w.1) ∧
        ∃ N : ℕ, x ≤ visibilityReplace N N (E w)} with hSdef
    have hdown : ∀ ⦃x y : Label.{u}⦄, x ≤ y → y ∈ S → x ∈ S := by
      rintro x y hxy (h | ⟨w, h1, h2, h3, N, hN⟩)
      · exact .inl (le_bot_iff.mp (h ▸ hτ.monotone hxy))
      · exact .inr ⟨w, h1, h2, h3, N, hxy.trans hN⟩
    have hvr : ∀ x ∈ S, ∀ k, ∀ i ≤ k, visibilityReplace k i x ∈ S := by
      rintro x (h | ⟨w, h1, h2, h3, N, hN⟩) k i hi
      · exact .inl (hτ.apply_visibilityReplace_eq_bot h k hi)
      · refine .inr ⟨w, h1, h2, h3, max N k, ?_⟩
        calc visibilityReplace k i x
            ≤ visibilityReplace (max N k) (max N k) (visibilityReplace k i x) :=
              le_visibilityReplace (by omega) _
          _ = visibilityReplace (max N k) (max N k) x :=
              visibilityReplace_self_visibilityReplace_of_le hi (le_max_right N k) x
          _ ≤ visibilityReplace (max N k) (max N k) (visibilityReplace N N (E w)) :=
              monotone_visibilityReplace le_rfl hN
          _ = visibilityReplace (max N k) (max N k) (E w) :=
              visibilityReplace_self_visibilityReplace_of_le le_rfl (le_max_left N k) _
    have hcomm : ∀ x, ∀ k ≤ D.grade s, ∀ i ≤ k,
        τ (visibilityReplace k i x) = visibilityReplace k i (τ x) := fun x k hk i hi ↦
      hτ.visibilityReplace_comm x k (le_top.trans_eq (stepSuppressor_of_le hk).symm) i hi
    obtain ⟨ρ, hρ, hρS, hρf⟩ := exists_isWitness_interpolation (f := τ) (m := D.grade s)
      hτ.map_bot hτ.monotone hcomm hdown hvr
    refine ⟨_, ρ, hρ, fun w ↦ ?_⟩
    change min (lowCut t (d.label w.1)) (d.label s) =
      min (ρ (E w)) (stepSuppressor (D.grade s) (D.grade w.1))
    rw [show stepSuppressor (D.grade s) (D.grade w.1) = ⊤ from stepSuppressor_of_le w.2.2,
      min_top_right, ← lowCut_min hsl]
    have hτw : τ (E w) = min (d.label w.1) (d.label s) := hτE w
    rw [← hτw]
    by_cases hS : E w ∈ S
    · rw [hρS _ hS]
      rcases hS with h0 | ⟨w', h1, h2, h3, N, hN⟩
      · exact lowCut_eq_bot_of_le le_rfl (.inl h0)
      rcases le_total (E w) (E w') with hle | hle
      · refine lowCut_eq_bot_of_le (hτ.monotone hle) (.inr ?_)
        have hτw' : τ (E w') ≤ d.label w'.1 := (hτE w').le.trans (min_le_left _ _)
        exact ⟨ne_top_of_le_ne_top h2 hτw', h3.mono hτw'⟩
      · have hτle : τ (E w) ≤ d.label w.1 := hτw.le.trans (min_le_left _ _)
        exact lowCut_eq_bot_of_le hτle (hsep s w' w hs0 hsl h1 h2 h3 hle ⟨N, hN⟩)
    · have hne : τ (E w) ≠ ⊥ := fun h ↦ hS (.inl h)
      rw [hρf _ hS hne]
      refine lowCut_of_not fun ⟨hnt, hb⟩ ↦ hS (.inr ⟨w, ?_, ?_, ?_, 0, le_visibilityReplace
        (by omega) _⟩)
      · intro h
        exact hne (by rw [hτw, h, min_eq_left bot_le])
      · rcases min_choice (d.label w.1) (d.label s) with h | h
        · rw [hτw, h] at hnt
          exact hnt
        · rw [hτw, h] at hnt hb
          exact absurd ⟨hnt, hb⟩ hsl
      · rcases min_choice (d.label w.1) (d.label s) with h | h
        · rw [hτw, h] at hb
          exact hb
        · rw [hτw, h] at hnt hb
          exact absurd ⟨hnt, hb⟩ hsl
  · -- availability
    obtain ⟨u, hu, hle⟩ := hd.availability s s' hss hg
    exact ⟨u, hu, lowCut_mono hle⟩

/-- **The rows separate the low labels by blocks when their offsets are at most the grade.**  If
every ordinal value `μ + j` (`μ` zero or a limit) of the row of a cell `s` of `d` has `j` at most
the grade of `s`, then `d` separates the low labels by blocks: a read `e` in the block of a low
read `w`, at or above it, is a replacement at the grade of `s` of the reading of `w` (or equal to
it), and the capped witness of the locality at `s` commutes with that replacement, which keeps a
label below the root blocks. -/
theorem lowBlockSeparated_of_rowOffsets {d : StageType.{u} α (n + 1)}
    (hoff : ∀ (s : Fin d.card) (w : d.toCellScheme.below (d.toCellScheme.gradedIndex s))
      (μ : Ordinal.{u}) (j : ℕ), Order.IsSuccPrelimit μ →
        d.rows.row s w = ((μ + j : Ordinal.{u}) : Label.{u}) → j ≤ d.toCellScheme.grade s) :
    LowBlockSeparated t d := by
  intro s w e hs0 hsl h1 h2 h3 hle ⟨N, hN⟩
  obtain ⟨τ, hτ, -, hτE⟩ := (d.isLawful.locality s).exists_isWitness_capped
    (p := fun w : d.toCellScheme.below (d.toCellScheme.gradedIndex s) ↦ d.label w.1)
    (c := ⟨s, d.toCellScheme.mem_below_gradedIndex s⟩) (fun w ↦ w.2.2)
    (d.isLawful.orderly s)
  have hτw : τ (d.rows.row s w) = min (d.label w.1) (d.label s) := hτE w
  have hτe : τ (d.rows.row s e) = min (d.label e.1) (d.label s) := hτE e
  suffices key : τ (d.rows.row s e) = ⊥ ∨
      (τ (d.rows.row s e) ≠ ⊤ ∧ BelowRootBlocks t (τ (d.rows.row s e))) by
    rcases min_choice (d.label e.1) (d.label s) with h | h
    · rwa [hτe, h] at key
    · rw [hτe, h] at key
      rcases key with k | k
      · exact absurd k hs0
      · exact absurd k hsl
  have hlw : τ (d.rows.row s w) = ⊥ ∨
      (τ (d.rows.row s w) ≠ ⊤ ∧ BelowRootBlocks t (τ (d.rows.row s w))) := by
    have hle' : τ (d.rows.row s w) ≤ d.label w.1 := hτw.le.trans (min_le_left _ _)
    by_cases hb : τ (d.rows.row s w) = ⊥
    · exact .inl hb
    · exact .inr ⟨ne_top_of_le_ne_top h2 hle', h3.mono hle'⟩
  have hEw0 : d.rows.row s w ≠ ⊥ := fun h ↦ by
    rw [h, hτ.map_bot] at hτw
    exact h1 ((min_eq_bot.mp hτw.symm).resolve_right hs0)
  have hcoded (x : d.toCellScheme.below (d.toCellScheme.gradedIndex s)) :
      d.rows.row s x ≠ ⊤ := fun h ↦ by
    have := d.isCoded s x
    rw [h] at this
    exact absurd this (not_lt.mpr le_top)
  obtain ⟨o, ho⟩ : ∃ o : Ordinal.{u}, d.rows.row s w = o := by
    induction hx : d.rows.row s w using recBotCoeTop with
    | bot => exact absurd hx hEw0
    | top => exact absurd hx (hcoded w)
    | coe o => exact ⟨o, rfl⟩
  obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
  have hvrlt : visibilityReplace N N (d.rows.row s w) <
      (((μ + Ordinal.omega0 : Ordinal.{u})) : Label.{u}) := by
    rw [ho]
    have hm : ∃ m : ℕ, visibilityReplace N N ((μ + j : Ordinal.{u}) : Label.{u}) =
        ((μ + m : Ordinal.{u}) : Label.{u}) := by
      by_cases hjN : j < N
      · exact ⟨N, visibilityReplace_coe_add_natCast hμ hjN N⟩
      · exact ⟨j, (isSelfVisible_coe_add_natCast_iff hμ).mpr (not_lt.mp hjN)⟩
    obtain ⟨m, hm⟩ := hm
    rw [hm]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (add_lt_add_right (Ordinal.natCast_lt_omega0 m) μ))
  obtain ⟨o', ho'⟩ : ∃ o' : Ordinal.{u}, d.rows.row s e = o' := by
    induction hx : d.rows.row s e using recBotCoeTop with
    | bot => exact absurd (le_bot_iff.mp (hx ▸ hle)) hEw0
    | top => exact absurd hx (hcoded e)
    | coe o => exact ⟨o, rfl⟩
  have hμo' : μ ≤ o' := by
    have h := hle
    rw [ho, ho'] at h
    exact le_self_add.trans (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))
  have ho'lt : o' < μ + Ordinal.omega0 := by
    have h := hN.trans_lt hvrlt
    rw [ho'] at h
    exact WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)
  obtain ⟨j', rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hμo' ho'lt
  have hj'g : j' ≤ d.toCellScheme.grade s := hoff s e μ j' hμ ho'
  have hjj : j ≤ j' := by
    have h := hle
    rw [ho, ho'] at h
    exact_mod_cast (add_le_add_iff_left μ).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))
  by_cases hjg : j < d.toCellScheme.grade s
  · have he : d.rows.row s e = visibilityReplace (d.toCellScheme.grade s) j' (d.rows.row s w) := by
      rw [ho, ho', visibilityReplace_coe_add_natCast hμ hjg]
    have hc := hτ.visibilityReplace_comm (d.rows.row s w) (d.toCellScheme.grade s)
      (le_top.trans_eq (stepSuppressor_of_le le_rfl).symm) j' hj'g
    rw [he, hc]
    rcases hlw with hb | ⟨hnt, hbr⟩
    · exact .inl (by rw [hb, visibilityReplace_bot])
    · exact .inr ⟨by simpa using hnt, fun x μ i hμ hx ↦
        (visibilityReplace_lt_iff hμ).mpr (hbr x μ i hμ hx)⟩
  · have he : d.rows.row s e = d.rows.row s w := by
      rw [ho, ho']
      have : j' = j := by omega
      rw [this]
    rw [he]
    exact hlw

/-- **The low truncation is lawful only when the rows separate the low labels by blocks.**  At a
failure `(s, w, e)` of the separation, a witness of the truncated locality at `s` is `⊥` at the
reading of `w` (the truncation is `⊥` at `w` and not `⊥` at `s`, so the suppressor is not `⊥` at
the grade of `w`), hence on its block (zero sets of witnesses are closed under the replacements
and downward), hence at the reading of `e`, while the truncation is not `⊥` at `e` or at `s`. -/
theorem lowBlockSeparated_of_isLawful_lowTruncation {d : StageType.{u} α (n + 1)}
    (h : d.rows.IsLawful (lowTruncation t d)) : LowBlockSeparated t d := by
  intro s w e hs0 hsl h1 h2 h3 hle ⟨N, hN⟩
  by_contra hne
  have he0 : d.label e.1 ≠ ⊥ := fun h ↦ hne (.inl h)
  have hel : ¬ (d.label e.1 ≠ ⊤ ∧ BelowRootBlocks t (d.label e.1)) := fun h ↦ hne (.inr h)
  obtain ⟨gρ, ρ, hρ, heq⟩ := h.locality s
  have hts : lowTruncation t d s = d.label s := lowCut_of_not hsl
  have hte : lowTruncation t d e.1 = d.label e.1 := lowCut_of_not hel
  have htw : lowTruncation t d w.1 = ⊥ := lowCut_of_low ⟨h2, h3⟩
  have hsc : s ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex s) :=
    d.toCellScheme.mem_below_gradedIndex s
  have hS := heq ⟨s, hsc⟩
  have hW := heq w
  have hE := heq e
  change min (lowTruncation t d s) (lowTruncation t d s) = min (ρ (d.rows.row s ⟨s, hsc⟩))
    (gρ (d.toCellScheme.grade s)) at hS
  change min (lowTruncation t d w.1) (lowTruncation t d s) = min (ρ (d.rows.row s w))
    (gρ (d.toCellScheme.grade w.1)) at hW
  change min (lowTruncation t d e.1) (lowTruncation t d s) = min (ρ (d.rows.row s e))
    (gρ (d.toCellScheme.grade e.1)) at hE
  rw [hts, min_self] at hS
  have hgs : gρ (d.toCellScheme.grade s) ≠ ⊥ := fun h0 ↦ hs0 (by rw [hS, h0, min_bot_right])
  have hgw : gρ (d.toCellScheme.grade w.1) ≠ ⊥ := fun h0 ↦
    hgs (le_bot_iff.mp (h0 ▸ hρ.antitone w.2.2))
  rw [htw, min_bot_left] at hW
  have hρw : ρ (d.rows.row s w) = ⊥ := (min_eq_bot.mp hW.symm).resolve_right hgw
  have hρe : ρ (d.rows.row s e) = ⊥ := le_bot_iff.mp
    ((hρ.apply_visibilityReplace_eq_bot hρw N le_rfl) ▸ hρ.monotone hN)
  rw [hte, hts, hρe, min_bot_left] at hE
  rcases min_eq_bot.mp hE with h' | h'
  · exact he0 h'
  · exact hs0 h'

/-- **The low truncation is lawful exactly when the rows separate the low labels by blocks.** -/
theorem isLawful_lowTruncation_iff {d : StageType.{u} α (n + 1)} :
    d.rows.IsLawful (lowTruncation t d) ↔ LowBlockSeparated t d :=
  ⟨lowBlockSeparated_of_isLawful_lowTruncation, isLawful_lowTruncation⟩

/-- **Legality does not bound the row offsets by the grade**: the one-point scheme with one cell
of grade `1` whose row reads it at `5` is legal (`SmallArityExamples.isLegal_onePointScheme`). -/
theorem exists_isLegal_rowOffset_gt_grade :
    ∃ S : Scheme.{u} 1, S.IsLegal ∧ ∃ (s : Fin S.card)
      (w : S.toCellScheme.below (S.toCellScheme.gradedIndex s)),
        S.rows.row s w = ((5 : ℕ) : Label.{u}) ∧ S.toCellScheme.grade s + 1 < 5 := by
  refine ⟨SmallArityExamples.onePointScheme 1 fun _ ↦ ((5 : ℕ) : Label.{u}),
    SmallArityExamples.isLegal_onePointScheme one_pos (fun _ _ _ ↦ le_rfl) (fun _ ↦ ?_)
      (fun _ ↦ ?_), ⟨0, one_pos⟩, ⟨⟨0, one_pos⟩, CellScheme.mem_below_gradedIndex _ _⟩, rfl, ?_⟩
  · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 5, by simp⟩)
  · exact (isSelfVisible_natCast 5).mpr (by omega)
  · change 1 + 1 < 5
    omega

/-- **The weakened lower bound at the root from the separation by blocks**
(`H3.isLawful_lowTruncation`). -/
theorem rootLowBound'_of_lowBlockSeparated {k : ℕ} {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)} (ht' : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces) {g : Fin n ↪ Fin k}
    (hpt : restrictFace g p = some t) {d : StageType.{u} α (n + 1)}
    {f : ProfileTower.Prof (seed ht' hp htb)} (h : LowBlockSeparated t d) :
    RootLowBound' n ht' hp htb hpt d f :=
  .inr (isLawful_lowTruncation h)

/-- **A witness matching a small prescription is `⊥` below its block.**  Let `Φ` be a witness
bounded by a grade `K ≥ n + 1` agreeing with `ψ` at a root cell `x` capped at a label
`θ ≥ n + 1`, with `ψ x < n + 1` and the label of `x` in the block of `μ` (`μ` zero or a limit).
Then `Φ` is `⊥` at every label below `μ`: such a label `y` lies below its replacement at `K`,
self-visible at `K`, which `Φ` sends to a label self-visible at `n + 1` and below `n + 1`.  So
every witness image of `d.label` matching the prescription is `⊥` at the cells of `d` labelled
below the block of `x`, and is lawful only if some lawful labelling of `d` is `⊥` there
(`CellScheme.Rows.isLawful_comp_iff_exists_bot_iff`). -/
theorem witness_eq_bot_below_block {ψ : Fin t.card → Label.{u}} {θ : Label.{u}} {K : ℕ}
    (hK : n + 1 ≤ K) {Φ : Label.{u} → Label.{u}} (hΦ : IsWitness (stepSuppressor K) Φ)
    (hθ : (((n + 1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤ θ) {x : Fin t.card}
    (hroot : min (Φ (t.label x)) θ = min (ψ x) θ)
    (hψ : ψ x < (((n + 1 : ℕ) : Ordinal.{u}) : Label.{u})) {μ : Ordinal.{u}} {i : ℕ}
    (hμ : Order.IsSuccPrelimit μ) (hx : t.label x = ((μ + i : Ordinal.{u}) : Label.{u}))
    {y : Label.{u}} (hy : y < ((μ : Ordinal.{u}) : Label.{u})) : Φ y = ⊥ := by
  have hψθ : ψ x < θ := hψ.trans_le hθ
  have hΦx : Φ (t.label x) = ψ x := by
    rw [min_eq_left hψθ.le] at hroot
    rcases min_choice (Φ (t.label x)) θ with h | h
    · rw [h] at hroot
      exact hroot
    · rw [h] at hroot
      exact absurd hroot hψθ.ne'
  set y' := visibilityReplace K K y
  have hy' : y' ≤ t.label x := by
    rw [hx]
    refine ((visibilityReplace_lt_iff hμ).mpr hy).le.trans ?_
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  have hsv : IsSelfVisible (n + 1) (Φ y') :=
    (hΦ.isSelfVisible_apply (isSelfVisible_visibilityReplace_self K y)
      (by rw [stepSuppressor_of_le le_rfl]; exact le_top)).mono hK
  have hle : Φ y' ≤ ψ x := hΦx ▸ hΦ.monotone hy'
  have hbot : Φ y' = ⊥ := by
    by_contra hne
    exact absurd ((natCast_le_of_isSelfVisible hsv hne).trans hle) (not_le.mpr hψ)
  exact le_bot_iff.mp (hbot ▸ hΦ.monotone (le_visibilityReplace (by omega) y))

end H3

end VaughtConjecture

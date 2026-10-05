/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.TiedApex
import VaughtConjecture.Extension.TwoFaceLift
import VaughtConjecture.Realization.BlockStages

/-!
# Forcing donors from the doubling chain: one-point types at low thresholds

Roadmap, Layer 3 (the finite construction for forcing donors), for Layer 4, output 2
(`ForcingDonors`, in `VaughtConjecture.Continuation.Normalization`); semantic contract, items 3–4.

Write `λ_η = blockStage η`.  An input of the forcing-donor property at `η` is a legal stage type
`t` at `λ_{η+1}` on `k` points, a cell `d` of `t` reducing to the formal top at `λ_η`, so that its
label is `λ_η + j` for some `j : ℕ` or the formal top (`j = ∞`; `StageType.label_mem_block`), and a
threshold `n ≤ j`.  A **forcing donor** for it is a legal `D` at `λ_{η+1}` on `m` points with `t`
as its face along some `g : Fin k ↪ Fin m`, such that `(D↓, g)` forces `n` at `d`, where `↓` is
reduction to `λ_η` (`StageType.ForcesThreshold`).  The donor is a stage type, and nothing here
involves a realization: the construction uses no uniqueness of expansions, no (R1), no receiving,
and no termination.

**The forcing-donor property is not proved in general.**  What is proved:

* **One-point inputs, `n ≤ 4`, unconditionally** (`forcingDonors_onePoint`).
* **One-point inputs at every `n`, given completions up to the arity `n - 2`**
  (`forcingDonors_onePoint_of_completions`).
* **Two-point inputs, through the doubling chain**, when the label of `d` is at least
  `λ_η + max n 3` and `n ≤ 4`, unconditionally (`forcingDonors_twoPoint`).
* **Two-point inputs, through a face**: a cell carried from the first point, labelled at least
  `λ_η + 2`, at the threshold `2`, unconditionally (`forcingDonors_twoPoint_face`).
* **Inputs on `m₀ + 1` points whose face along `Fin.castSuccEmb` is defined**, when the label of
  `d` is at least `λ_η + max n (m₀ + 2)`, given completions up to the arity
  `max n (m₀ + 2) - 2` (`forcingDonor_of_completions`).

The trivial case `n ≤ grade d` holds with `D = t` (the order law,
`StageType.forcesThreshold_of_le_grade`).

**Completions.**  `CompletionsUpTo α M` says that every seed of two legal coatom types on
`m + 1 ≤ M + 1` points at the stage `α` (`Seed.ofCoatoms`) has a completion below the full grade:
the hypothesis of `StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`, restricted to
the arities `m ≤ M`.  It holds for `M = 2` (`completionsUpTo_two`, from
`Seed.nonempty_completionBelowFullGrade_of_le_two`); beyond, it is a hypothesis.  Only the seeds
`Seed.ofCoatoms` of a type with itself are used, and for one such seed a completion follows from the
two-face lifts `2FL(j)` at `2 ≤ j < m` (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift`).
The apex of the completion and its maximality are not used.

**The doubling chain** (`StageType.exists_doublingChain`,
`StageType.exists_isLegalBelowFullGrade_doublingChain`).  From a legal `t` on `m₀ + 1` points
with a defined face along `Fin.castSuccEmb`, complete the seed of `t` with itself, and repeat:
step `i` uses a completion at the arity `m₀ + i`, and its result is legal on `m₀ + i + 2` points
with the previous type as its face along the first coatom.  The truncation of the last completion
is legal below the full grade and has `t` as a face along a proper face; the tied apex over it
(`StageType.exists_donor_of_isLegalBelowFullGrade`, `VaughtConjecture.Extension.TiedApex`) is the
donor.  The tie needs the label of `d` self-visible at the number `N` of points of the donor,
that is `N ≤ j` (`Label.isSelfVisible_of_coe_add_le`).  For a one-point type, `N = max n 2`.

**The arity of a donor is set by the threshold, not by the input.**  A pair at `λ_{η+1}` forcing `n`
at a cell labelled the formal top has a cell of grade at least `n`, hence at least `n` points
(`StageType.not_forcesThreshold_of_grade_le`), and legal one-point inputs exist at every offset
(`OnePoint.le_of_forcingDonor`: for every `j ≥ 1`, a legal one-point type labelled `λ_η + j` all
of whose donors at the threshold `j` have at least `j` points; the type is
`StageType.exists_onePoint_label`).  So the forcing-donor property needs donors on arbitrarily many
points already for one-point types.  The construction from the unconditional completions at the
arities `m ≤ 2` gives donors on at most `4` points, hence the thresholds `n ≤ 4`; the statements
assert only that some donor exists (`∃ m`), not this bound.

**What remains.**  A tie cell `C` forcing `n` has its label at most that of `d` and at least `λ_η`
plus its grade (`StageType.forcesThreshold_of_row_le`), so its grade lies between `n` and `j`.

* *Top ties beyond the compiled cases.*  When `max n (#(scope d) + 1) ≤ j`, a tied apex over a
  type with the face of `t` at `scope d` as a face forces `n`.  For the doubling chain of `t` itself
  this needs `max n (k + 1) ≤ j` and the completions up to the arity `max n (k + 1) - 2`; for
  three or more points it also needs a reindexing of `t` to make its face along `Fin.castSuccEmb`
  defined.  Otherwise the donor of the face is to be amalgamated with `t` over the face
  (`StageType.exists_amalgam`, from `StageType.HasCoatomExtensions`).  Neither is compiled beyond
  the cases above.
* *The residual inputs*, with `grade d < n ≤ j ≤ #(scope d)`.  A **top tie** is a tie cell at the
  full graded index `(univ, N)` of a donor on `N` points having a face containing `scope d` along a
  proper face, as in the tied apex.  Its grade is `N ≥ #(scope d) + 1 > j`, so no top tie exists.
  The smallest residual input has two points: `d` at `({0, 1}, 1)`, labelled exactly `λ_η + 2`,
  with `n = 2`.  These inputs need a completion with one prescribed tie at an intermediate grade
  (prospective):

  **`TiedLayer`** (prospective): for a seed `I` at the arity `m`, a grade `j' < m + 2`, and an
  old cell `e` of grade at most `j'` whose glued label is self-visible at `j'`, a completion below
  the full grade of `I`, with its lawful labelling, having one further cell `C` at the graded
  index `(univ, j')` whose row is at most as large at `C` as at `e`, and labelled with the label
  of `e`.  The apex completion of it would force `j'` at `e`.

  The rows of the new cells of the tower (`Scheme.fieldRow`) take at their own cell the agreement
  height of an entry with itself, above every value at an old cell, so they tie no old cell: the
  library has no completion with a prescribed tie.  `TiedLayer` is not refuted.

**A tie is an upper bound only.**  A tie bounds the tied cell from above and prescribes nothing at
the other cells of its graded index.  In a capped lift, locality at the tied cell and the tie never
need a value above the cap (`Label.TransformsTo.cap_tied`).  This does not cover availability at
the graded index of the tied cell, which can still force it upward, nor the rows of the cells that
read it; so it is not shown that a tied cell escapes the mechanism by which bottom twins and
availability force a cell above two incomparable cells, the obstruction met by the gated pinned
extension property (`StageType.HasGatedPinnedExtensions`).

## Placement

Layer 3 of `roadmap/README.md` (the finite construction for forcing donors, Layer 4, output 2).
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Completions up to an arity -/

variable {α : Ordinal.{u}}

/-- **Completions of every seed of two coatom types up to the arity `M`** at the stage `α`: the
hypothesis of `StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`, restricted to the
arities `m ≤ M`.  It holds for `M ≤ 2` (`completionsUpTo_two`). -/
def CompletionsUpTo (α : Ordinal.{u}) (M : ℕ) : Prop :=
  ∀ m ≤ M, ∀ (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m) (hla : ta.IsLegal)
    (hlb : tb.IsLegal) (hpa : StageType.restrictFace Fin.castSuccEmb ta = some p)
    (hpb : StageType.restrictFace Fin.castSuccEmb tb = some p),
    Nonempty (CompletionBelowFullGrade (Seed.ofCoatoms hla hlb hpa hpb))

/-- **The completions up to the arity `2` exist**, at every stage. -/
theorem completionsUpTo_two : CompletionsUpTo α 2 := fun _ hm _ _ _ _ _ _ _ ↦
  Seed.nonempty_completionBelowFullGrade_of_le_two _ hm

/-- Completions up to an arity give completions up to every smaller arity. -/
theorem CompletionsUpTo.mono {M M' : ℕ} (h : CompletionsUpTo α M) (hM : M' ≤ M) :
    CompletionsUpTo α M' := fun m hm ↦ h m (hm.trans hM)

/-! ### The doubling chain -/

namespace StageType

variable {m₀ : ℕ} {t : StageType.{u} α (m₀ + 1)}

/-- **The doubling chain, legal stage types.**  From a legal `t` on `m₀ + 1` points whose face
along `Fin.castSuccEmb` is defined, completing the seed of a type with itself `r` times gives a
legal stage type on `m₀ + r + 1` points with `t` as a face and a defined face along
`Fin.castSuccEmb`, given completions up to the arity `m₀ + r - 1`. -/
theorem exists_doublingChain (hα : Order.IsSuccPrelimit α) (ht : t.IsLegal)
    (hp : ∃ p, restrictFace Fin.castSuccEmb t = some p) {M : ℕ} (hC : CompletionsUpTo α M) :
    ∀ r : ℕ, m₀ + r ≤ M + 1 → ∃ L : StageType.{u} α (m₀ + r + 1), L.IsLegal ∧
      (∃ p, restrictFace Fin.castSuccEmb L = some p) ∧
      ∃ g : Fin (m₀ + 1) ↪ Fin (m₀ + r + 1), restrictFace g L = some t
  | 0, _ => ⟨t, ht, hp, Function.Embedding.refl _, restrictFace_refl t⟩
  | r + 1, hr => by
    obtain ⟨L, hL, ⟨p, hLp⟩, g, hg⟩ := exists_doublingChain hα ht hp hC r (by omega)
    obtain ⟨F⟩ := hC (m₀ + r) (by omega) L L p hL hL hLp hLp
    refine ⟨F.completion hα, F.isLegal_completion hα, ⟨L, F.restrictFace_left_completion hα⟩,
      g.trans Fin.castSuccEmb, ?_⟩
    rw [← restrictFace_trans _ _ _ (F.restrictFace_left_completion hα)]
    exact hg

/-- **The doubling chain, a type legal below the full grade.**  Given completions up to the
arity `m₀ + r`, some stage type on `m₀ + r + 2` points legal below the full grade has `t` as its
face along a proper face. -/
theorem exists_isLegalBelowFullGrade_doublingChain (hα : Order.IsSuccPrelimit α) (ht : t.IsLegal)
    (hp : ∃ p, restrictFace Fin.castSuccEmb t = some p) {r : ℕ}
    (hC : CompletionsUpTo α (m₀ + r)) :
    ∃ T : StageType.{u} α (m₀ + r + 2), T.IsLegalBelowFullGrade ∧
      ∃ g : Fin (m₀ + 1) ↪ Fin (m₀ + r + 2), univ.map g ≠ univ ∧ restrictFace g T = some t := by
  obtain ⟨L, hL, ⟨p, hLp⟩, g, hg⟩ := exists_doublingChain hα ht hp hC r (by omega)
  obtain ⟨F⟩ := hC (m₀ + r) le_rfl L L p hL hL hLp hLp
  refine ⟨F.truncate hα, F.isLegalBelowFullGrade, g.trans (Coatom.left (m₀ + r)), ?_, ?_⟩
  · intro he
    have h := mem_univ (Fin.last (m₀ + r + 1))
    rw [← he, ← Finset.map_map] at h
    exact Coatom.last_notMem_univ_map_left (Finset.map_subset_map.mpr (subset_univ _) h)
  · rw [← restrictFace_trans _ _ _ (F.restrictFace_left_truncate hα)]
    exact hg

end StageType

/-! ### Forcing donors -/

section Forcing

variable {η : Ordinal.{u}}

/-- **Forcing donors from completions of the doubling chain.**  Let `t` be a legal type at
`λ_{η+1}` on `m₀ + 1` points whose face along `Fin.castSuccEmb` is defined, `d` a cell of `t`
reducing to the formal top, and `n` a threshold.  If the label of `d` is at least
`λ_η + max n (m₀ + 2)` and completions exist up to the arity `max n (m₀ + 2) - 2`, a forcing donor
exists: the tied apex over the doubling chain.  The construction gives a donor on `max n (m₀ + 2)`
points; the statement asserts only that some donor exists. -/
theorem forcingDonor_of_completions {m₀ : ℕ} {t : StageType.{u} (blockStage (η + 1)) (m₀ + 1)}
    (ht : t.IsLegal) (hp : ∃ p, StageType.restrictFace Fin.castSuccEmb t = some p)
    {d : Fin t.card} (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) {n : ℕ}
    (hn : ((blockStage η + max n (m₀ + 2) : Ordinal.{u}) : Label.{u}) ≤ t.label d)
    (hC : CompletionsUpTo (blockStage (η + 1)) (max n (m₀ + 2) - 2)) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin (m₀ + 1) ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d n := by
  obtain ⟨r, hr⟩ : ∃ r, max n (m₀ + 2) = m₀ + r + 2 :=
    ⟨max n (m₀ + 2) - (m₀ + 2), by omega⟩
  rw [hr] at hn hC
  have hC' : CompletionsUpTo (blockStage (η + 1)) (m₀ + r) := hC.mono (by omega)
  obtain ⟨T, hT, g, hg, hgt⟩ := StageType.exists_isLegalBelowFullGrade_doublingChain
    (isSuccPrelimit_blockStage (η + 1)) ht hp hC'
  have hblock := StageType.label_mem_block t hd
  obtain ⟨D, hD, hDt, hF⟩ := StageType.exists_donor_of_isLegalBelowFullGrade
    (isSuccPrelimit_blockStage η) hT (by omega) hg hgt hblock.1
    (Label.isSelfVisible_of_coe_add_le (isSuccPrelimit_blockStage η) hblock.2
      (by exact_mod_cast hn))
  exact ⟨_, D, g, hD, hDt, hF.mono (by omega)⟩

/-- **Forcing donors for one-point types at every threshold, given completions** up to the arity
`n - 2`: the type itself when `n ≤ 1` (the order law), and otherwise the tied apex over the
doubling chain of `t`, on `n` points. -/
theorem forcingDonors_onePoint_of_completions (t : StageType.{u} (blockStage (η + 1)) 1)
    (ht : t.IsLegal) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ)
    (hn : ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d)
    (hC : CompletionsUpTo (blockStage (η + 1)) (n - 2)) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 1 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d n := by
  rcases le_or_gt n 1 with h1 | h1
  · have hg : (t.reduce (isSuccPrelimit_blockStage η)).toCellScheme.grade d = 1 :=
      le_antisymm (t.grade_le d) (t.isWellFormed.isWellFormed.grade_pos d)
    exact ⟨1, t, Function.Embedding.refl _, ht, StageType.restrictFace_refl t,
      StageType.forcesThreshold_of_le_grade (StageType.restrictFace_refl _) hd
        (by rw [hg]; exact h1)⟩
  · have hmax : max n (0 + 2) = n := by omega
    exact forcingDonor_of_completions (m₀ := 0) ht
      (Option.isSome_iff_exists.mp (t.isSome_restrictFace_of_zero _)) hd (by rwa [hmax])
      (by rwa [hmax])

/-- **Forcing donors for one-point types, up to the threshold `4`, unconditionally.**  Every input
of `ForcingDonors η` on one point with `n ≤ 4` has a donor: the completions of the doubling chain
are at the arities `m ≤ 2`.  The construction gives a donor on at most `4` points; the statement
asserts only that some donor exists. -/
theorem forcingDonors_onePoint (t : StageType.{u} (blockStage (η + 1)) 1) (ht : t.IsLegal)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ)
    (hn : ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d) (hn4 : n ≤ 4) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 1 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d n :=
  forcingDonors_onePoint_of_completions t ht d hd n hn (completionsUpTo_two.mono (by omega))

/-- **Forcing donors for two-point types, through the doubling chain**: unconditionally when the
label of `d` is at least `λ_η + max n 3` and `n ≤ 4`. -/
theorem forcingDonors_twoPoint (t : StageType.{u} (blockStage (η + 1)) 2) (ht : t.IsLegal)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ)
    (hn : ((blockStage η + max n 3 : Ordinal.{u}) : Label.{u}) ≤ t.label d) (hn4 : n ≤ 4) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 2 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η)) d n :=
  forcingDonor_of_completions (m₀ := 1) ht (StageType.exists_restrictFace_castSuccEmb_of_two t) hd
    hn (completionsUpTo_two.mono (by omega))

/-- **Forcing donors for two-point types through a face**: a cell carried from the first point,
labelled at least `λ_η + 2`, is forced to `2` by the completion of the seed of `t` with the
two-point tied-apex donor of its first point; both completions are at the arities `0` and `1`.
This covers the label `λ_η + 2`, which the doubling chain of `t` (on three points) does not. -/
theorem forcingDonors_twoPoint_face (t : StageType.{u} (blockStage (η + 1)) 2) (ht : t.IsLegal)
    (hf : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ t.toCellScheme.faces)
    (d' : Fin (t.comap Fin.castSuccEmb hf).card)
    (hd : (t.reduce (isSuccPrelimit_blockStage η)).label (t.cellMap Fin.castSuccEmb d') = ⊤)
    (hn : ((blockStage η + 2 : Ordinal.{u}) : Label.{u}) ≤
      t.label (t.cellMap Fin.castSuccEmb d')) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 2 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
        (t.cellMap Fin.castSuccEmb d') 2 := by
  set hβ := isSuccPrelimit_blockStage η
  set hα := isSuccPrelimit_blockStage (η + 1)
  have ht'l : (t.comap Fin.castSuccEmb hf).IsLegal := ht.comap _ hf
  have htt' : StageType.restrictFace Fin.castSuccEmb t = some (t.comap Fin.castSuccEmb hf) :=
    StageType.restrictFace_of_mem t _ hf
  -- The donor of the first point: the tied apex over the doubling seed of its face.
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    ((t.comap Fin.castSuccEmb hf).isSome_restrictFace_of_zero Fin.castSuccEmb)
  obtain ⟨F₀⟩ := Seed.nonempty_completionBelowFullGrade_of_le_two
    (Seed.ofCoatoms ht'l ht'l hp₀ hp₀) (by omega)
  have hblock := StageType.label_mem_block t hd
  obtain ⟨E, hE, hEt', hFE⟩ := StageType.exists_donor_of_isLegalBelowFullGrade hβ
    F₀.isLegalBelowFullGrade (by omega) Coatom.univ_map_left_ne (F₀.restrictFace_left_truncate hα)
    (d := d') hblock.1 (Label.isSelfVisible_of_coe_add_le hβ hblock.2 (by exact_mod_cast hn))
  -- The completion of the seed of `t` with the donor `E` over `t'`.
  obtain ⟨F⟩ := Seed.nonempty_completionBelowFullGrade_of_le_two
    (Seed.ofCoatoms ht hE htt' hEt') (by omega)
  refine ⟨_, F.completion hα, Coatom.left 1, F.isLegal_completion hα,
    F.restrictFace_left_completion hα, ?_⟩
  have hDE : StageType.restrictFace (Coatom.right 1) ((F.completion hα).reduce hβ) =
      some (E.reduce hβ) := by
    -- `rfl`: `Option.map` on `some`, and the second coatom type of the seed is `E`
    rw [StageType.restrictFace_reduce, F.restrictFace_right_completion hα]; rfl
  have hDt : StageType.restrictFace (Coatom.left 1) ((F.completion hα).reduce hβ) =
      some (t.reduce hβ) := by
    -- `rfl`: `Option.map` on `some`, and the first coatom type of the seed is `t`
    rw [StageType.restrictFace_reduce, F.restrictFace_left_completion hα]; rfl
  have h1 := hFE.trans_face hDE
  rw [show (Fin.castSuccEmb : Fin 1 ↪ Fin 2).trans (Coatom.right 1) =
      (Fin.castSuccEmb : Fin 1 ↪ Fin 2).trans (Coatom.left 1) from
    castSuccEmb_trans_extendByLast _] at h1
  -- the reduction keeps the scheme (`reduce_toScheme`), hence the faces
  have hf' : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (t.reduce hβ).toCellScheme.faces := hf
  exact (StageType.ForcesThreshold.trans_comap_iff hDt hf' d').mp h1

end Forcing

/-! ### The arity of the donors of one-point types -/

namespace OnePoint

/-- **Donors of one-point types have unbounded arity.**  For every `j ≥ 1`, some legal one-point
type at `λ_{η+1}` labelled `λ_η + j` (`StageType.exists_onePoint_label`) is an input of
`ForcingDonors η` at the threshold `j`, and every donor for it, on `m` points, has `j ≤ m`
(`StageType.not_forcesThreshold_of_grade_le`). -/
theorem le_of_forcingDonor {η : Ordinal.{u}} {j : ℕ} (hj : 1 ≤ j) :
    ∃ t : StageType.{u} (blockStage (η + 1)) 1, t.IsLegal ∧
      ∃ d : Fin t.card, (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤ ∧
        ((blockStage η + j : Ordinal.{u}) : Label.{u}) ≤ t.label d ∧
        ∀ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 1 ↪ Fin m),
          StageType.restrictFace g D = some t →
          StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
            (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
            d j → j ≤ m := by
  have hβ := isSuccPrelimit_blockStage η
  have hlt (i : ℕ) : blockStage η + i < blockStage (η + 1) := by
    rw [blockStage_add_one]; exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)
  obtain ⟨t, ht, d, -, htd⟩ := StageType.exists_onePoint_label (α := blockStage (η + 1))
    (isSelfVisible_coe_add hβ hj) (hlt j)
  have hβd : (t.reduce hβ).label d = ⊤ := by
    rw [StageType.reduce_label, htd]
    exact Label.reduce_eq_top_iff.mpr (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))
  refine ⟨t, ht, d, hβd, htd.ge, fun m D g hgD h ↦ ?_⟩
  by_contra hjm
  have hD : StageType.restrictFace g (D.reduce hβ) = some (t.reduce hβ) := by
    rw [StageType.restrictFace_reduce, hgD, Option.map_some]
  exact StageType.not_forcesThreshold_of_grade_le (hlt m) (fun c ↦ D.grade_le c) hD hβd
    (h.mono (by omega))

end OnePoint

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.BlockStages
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Model
import VaughtConjecture.Stage.Threshold

/-!
# Normalization: the stable label as a supremum over rooted covers

Roadmap, Layer 4, outputs 1–2 of higher-stage reconstruction (the stable values of the provisional
observations on actual rooted covers, and normalization); semantic contract, items 7 and 12.

Throughout, `λ_η = blockStage η` and `λ_{η+1} = λ_η + ω` are consecutive block stages, `R` is a
realization at `λ_{η+1}` on a carrier `M`, and `S := R↓λ_η` is its stage reduction.  Let `c` cover
a stage type `t` in `R` (`Realization.Covers`), with **root** `p := t↓λ_η`, and let `d` be a cell
of `t` whose reduction to `λ_η` is the formal top; its label lies in the block `[λ_η, λ_η + ω)` or
is the formal top (`StageType.label_mem_block`).

**Rooted covers.**  A **rooted cover** of `c` in `S` is a triple `x = (m, q, f)` — a stage type
`q` at `λ_η` on `m` points and an embedding `f : Fin k ↪ Fin m` — such that `c` extends to a cover
of `x` in `S` (`Realization.ExtendsToCover`): some tuple `s` covering `q` in `S` has `s ∘ f = c`.
A tuple with a repeated coordinate has no rooted cover (`Realization.ExtendsToCover.injective`).

**Forcing and the provisional offset** (`VaughtConjecture.Stage.Threshold`).  A rooted cover
`(m, q, f)` **forces** the threshold `n` at `d` when every stage type at `λ_{η+1}` reducing to `q`
has, on its face along `f`, a label at least `λ_η + n` at `d`
(`StageType.ForcesThreshold`).  The **provisional offset** of `d` at the cover is the supremum in
`ℕ∞` of the thresholds forced (`StageType.provisionalOffset`); it depends only on `(q, f, p, d)`.

**The stable offset and the stable label.**  The **stable offset** of `d` at `c` in `S`
(`Realization.stableOffset`) is the supremum, over the rooted covers of `c` in `S`, of their
provisional offsets, and the **stable label** (`Realization.stableLabel`) is `λ_η + n` for a finite
stable offset `n` and the formal top for the stable offset `⊤` (`Label.ofOffset`), never
`λ_η + ω`.  The stable value is thus a **supremum over rooted covers** of an offset determined by
finite data: the cover's type at `λ_η`, the coordinate embedding and the transported cell.
Forcing only grows along extensions of rooted covers (`StageType.ForcesThreshold.trans_face`,
which uses face maps and stage reduction alone; in an exactly consistent realization the type of
a rooted cover restricts to that of a smaller one along the coordinates), so the provisional
offsets never decrease along extensions, and an eventual-value construction that allows decreases
does not arise.  The identification of the supremum with an eventual value along a directed
family of rooted covers is not needed by any statement here and is not formalized.

**Results.**

* **Soundness** (`Realization.Covers.le_label_of_forcesThreshold`), unconditional: under exact
  consistency alone, a rooted cover forcing `n` at `d` gives `λ_η + n ≤ t.label d`.  It holds for
  any stages `β ≤ α`, `β` zero or a limit.
* **Realizing a donor's reduction**
  (`Realization.HasFiniteExtensionReceiving.extendsToCover_reduce`): with finite-extension
  receiving, for a legal stage type `D` at the stage of `R` whose face along `g` is `t`, the
  reduction of `D`, with `g`, is a rooted cover of `c`.  Only the cutoff `λ_η` is
  used, and only the reduction of the received type is read: a member of the receiving family at
  `λ_η` has the reduction of the donor (`StageType.reduce_eq_of_mem_receivingFamily`).  This is not
  exact projected receiving (semantic contract, item 12).
* **Forcing donors** (`ForcingDonors η`), a finite statement about legal stage types with no
  realization: whenever a legal `t` at `λ_{η+1}` has label at least `λ_η + n` at a cell `d`
  reducing to the formal top, some legal `D` at `λ_{η+1}` has `t` as its face along some `g`, and
  `(D↓λ_η, g)` forces `n` at `d`.  It is still to be proved: a finite construction of Layer 3 (new
  points, a full-scope cell tied to `d` by its row, and completeness above it), blocked on the
  completion below the full grade, not on (R1).  Its case `n ≤` the grade of `d` holds with
  `D = t` by the order law (`StageType.forcesThreshold_of_le_grade`).
* **The threshold lemma** (`Realization.le_label_iff_exists_forcesThreshold`): for `R` exactly
  consistent, with legal types and finite-extension receiving, and given forcing donors at `η`,
  `λ_η + n ≤ t.label d` exactly when some rooted cover of `c` in `R↓λ_η` forces `n` at `d`.  The
  right side depends on `R` only through `R↓λ_η`.  Soundness gives one direction; forcing donors
  and receiving the donor's reduction give the other.
* **Normalization of labels** (`Realization.label_eq_stableLabel`), under the same hypotheses: the
  label of `d` is the stable label, by `Label.eq_of_forall_threshold_iff`.
* **Determination by the reduction** (`Realization.eq_of_reduce_eq_of_forcingDonors`): two exactly
  consistent realizations at `λ_{η+1}` with legal types, finite-extension receiving and equal
  reductions to `λ_η` are equal, given forcing donors at `η`; by `Realization.ext` and
  `StageType.eq_of_reduce_eq_of_threshold_iff`.

**Conditional and unconditional.**  Soundness is unconditional.  Completeness — the threshold
lemma, normalization of labels and determination by the reduction — is conditional on
finite-extension receiving of the realizations at `λ_{η+1}`, which follows from (R1) of the table
of Layer 3 (finite-cut receiving of models; still to be proved), and on forcing donors at `η`
(still to be proved).  The four extension clauses of a model enter only through (R1).

**What is not assumed or claimed.**

* No uniqueness or coherence of expansions is assumed: determination by the reduction is proved,
  for any two realizations satisfying the hypotheses.
* No global termination: the stable offset `⊤` (unbounded growth along the rooted covers) is
  allowed, and decodes to the formal top, not to `λ_η + ω`.
* No exact projected receiving and no lifting of projected donors: donors live at `λ_{η+1}`, the
  single cutoff `λ_η` is used, and only the reduction of a received type is read.
* No existence: normalization says that every realization satisfying the hypotheses carries the
  stable labels, not that one exists; the domain guard is not given here.  Lawfulness of the stable
  labelling as a stage type at every typed tuple, when no realization is given (output 1, the
  candidate realization), and the modelhood criterion (output 3) are not proved here.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Ordinal

namespace Realization

variable {α β : Ordinal.{u}} {M : Type v} {k : ℕ}

/-! ### Rooted covers and soundness -/

/-- A tuple that extends to a cover is injective: a tuple with a repeated coordinate has no rooted
cover. -/
theorem ExtendsToCover.injective {S : Realization.{u, v} β M} {c : Fin k → M}
    {x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)} (h : S.ExtendsToCover c x) :
    Function.Injective c := by
  obtain ⟨s, rfl, hs⟩ := h
  exact hs.injective.comp x.2.2.injective

/-- **Soundness** (unconditional): under exact consistency, if `c` covers `t` in `R` and a rooted
cover of `c` in the reduction of `R` to `β` forces `n` at `d`, then the label of `d` in `t` is at
least `β + n`. -/
theorem Covers.le_label_of_forcesThreshold {R : Realization.{u, v} α M} (hR : R.IsConsistent)
    (hβ : Order.IsSuccPrelimit β) {t : StageType.{u} α k} {c : Fin k → M} (hc : R.Covers t c)
    {d : Fin t.card} {n : ℕ} {x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)}
    (hx : StageType.ForcesThreshold α hβ x.2.1 x.2.2 (t.reduce hβ) d n)
    (hcov : (R.reduce hβ).ExtendsToCover c x) :
    ((β + n : Ordinal.{u}) : Label.{u}) ≤ t.label d := by
  obtain ⟨s, hsc, hs, hsq⟩ := hcov
  rw [reduce_eval, Option.map_eq_some_iff] at hsq
  obtain ⟨Q, hQ, hQq⟩ := hsq
  have hface : R.eval (x.2.2.trans ⟨s, hs⟩) = StageType.restrictFace x.2.2 Q := hR _ Q x.2.2 hQ
  have hct : x.2.2.trans ⟨s, hs⟩ = ⟨c, hc.injective⟩ := by
    ext i
    exact congrFun hsc i
  rw [hct, hc.eval_eq] at hface
  exact hx.2 Q t hQq hface.symm d rfl

/-- **Realizing a donor's reduction**: with finite-extension receiving, if `c` covers `t` in `R`
and `t` is the face along `g` of a legal stage type `D` at the stage of `R`, then the reduction of
`D` to a permitted cutoff `β` that is zero or a limit, with `g`, is a rooted cover of `c` in the
reduction of `R` to `β`. -/
theorem HasFiniteExtensionReceiving.extendsToCover_reduce {R : Realization.{u, v} α M}
    (hrec : R.HasFiniteExtensionReceiving) (hβ : Order.IsSuccPrelimit β)
    (hβα : Label.IsPermittedCutoff α (β : Label.{u})) {t : StageType.{u} α k} {c : Fin k → M}
    (hc : R.Covers t c) {m : ℕ} {D : StageType.{u} α m} {g : Fin k ↪ Fin m} (hD : D.IsLegal)
    (hg : StageType.restrictFace g D = some t) :
    (R.reduce hβ).ExtendsToCover c ⟨m, D.reduce hβ, g⟩ := by
  obtain ⟨u, hu, Q, hQ, huQ⟩ := hrec ⟨c, hc.injective⟩ t hc.eval_eq D g hD hg β hβα
  refine ⟨u, funext fun i ↦ DFunLike.congr_fun hu i, covers_of_eval u ?_⟩
  rw [reduce_eval, huQ, Option.map_some, StageType.reduce_eq_of_mem_receivingFamily hβ hQ]

end Realization

/-! ### Forcing donors -/

/-- **Forcing donors** at the block index `η`: for every legal stage type `t` at `λ_{η+1}`, every
cell `d` of `t` reducing to the formal top at `λ_η` and every `n` with `λ_η + n ≤ t.label d`, some
legal stage type `D` at `λ_{η+1}` has `t` as its face along some `g`, and `(D↓λ_η, g)` forces `n`
at `d`.  A finite statement about stage types, with no realization.  It is still to be proved: a
finite construction of Layer 3, blocked on the completion below the full grade, not on (R1). -/
def ForcingDonors (η : Ordinal.{u}) : Prop :=
  ∀ ⦃k : ℕ⦄ (t : StageType.{u} (blockStage (η + 1)) k), t.IsLegal → ∀ d : Fin t.card,
    (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤ → ∀ n : ℕ,
      ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d →
        ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin k ↪ Fin m),
          D.IsLegal ∧ StageType.restrictFace g D = some t ∧
          StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
            (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η)) d n

namespace Realization

variable {α β : Ordinal.{u}} {M : Type v} {k : ℕ}

/-! ### The threshold lemma -/

section Threshold

variable {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}
  {t : StageType.{u} (blockStage (η + 1)) k} {c : Fin k → M}

/-- **The threshold lemma**, conditional on finite-extension receiving (from (R1), still to be
proved) and on forcing donors at `η` (still to be proved): if `c` covers `t` in `R` and the cell
`d` of `t` reduces to the formal top at `λ_η`, then the label of `d` is at least `λ_η + n` exactly
when some rooted cover of `c` in the reduction of `R` to `λ_η` forces `n` at `d`.  Hypotheses by
use: `hR` (soundness, from right to left); `hl`, `hd` and `hF` (the donor, from left to right);
`hrec` (realizing the donor's reduction, from left to right); `hc` (both directions). -/
theorem le_label_iff_exists_forcesThreshold (hR : R.IsConsistent) (hl : R.HasLegalTypes)
    (hrec : R.HasFiniteExtensionReceiving) (hF : ForcingDonors.{u} η) (hc : R.Covers t c)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ) :
    ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d ↔
      ∃ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
        StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) x.2.1 x.2.2
          (t.reduce (isSuccPrelimit_blockStage η)) d n ∧
        (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hcov⟩ ↦ hc.le_label_of_forcesThreshold hR _ hx hcov⟩
  obtain ⟨m, D, g, hD, hg, hforce⟩ := hF t (hl _ t hc.eval_eq) d hd n h
  exact ⟨⟨m, D.reduce _, g⟩, hforce,
    hrec.extendsToCover_reduce _ (isPermittedCutoff_blockStage η) hc hD hg⟩

end Threshold

/-! ### The stable offset and the stable label -/

section Stable

variable (S : Realization.{u, v} β M) (α) (hβ : Order.IsSuccPrelimit β) (c : Fin k → M)
  (p : StageType.{u} β k) (d : Fin p.card)

/-- The **stable offset** of the cell `d` of the root `p` at `c` in `S`: the supremum, over the
rooted covers of `c` in `S`, of their provisional offsets. -/
noncomputable def stableOffset : ℕ∞ :=
  ⨆ (x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)) (_ : S.ExtendsToCover c x),
    StageType.provisionalOffset α hβ x.2.1 x.2.2 p d

/-- The **stable label** of the cell `d` of the root `p` at `c` in `S`: `β + n` for a finite
stable offset `n`, and the formal top for the stable offset `⊤`. -/
noncomputable def stableLabel : Label.{u} :=
  Label.ofOffset β (S.stableOffset α hβ c p d)

variable {S α hβ c p d}

/-- Equal roots and cells at equal positions have the same stable offset. -/
theorem stableOffset_congr {p' : StageType.{u} β k} (h : p = p') {d' : Fin p'.card}
    (hd : (d : ℕ) = d') : S.stableOffset α hβ c p d = S.stableOffset α hβ c p' d' := by
  subst h
  rw [Fin.ext hd]

/-- Equal roots and cells at equal positions have the same stable label. -/
theorem stableLabel_congr {p' : StageType.{u} β k} (h : p = p') {d' : Fin p'.card}
    (hd : (d : ℕ) = d') : S.stableLabel α hβ c p d = S.stableLabel α hβ c p' d' := by
  rw [stableLabel, stableLabel, stableOffset_congr h hd]

/-- **The thresholds of the stable offset**: if `c` covers the root `p` in `S` and `d` is
labelled the formal top in `p`, then `n` is at most the stable offset exactly when some rooted
cover of `c` in `S` forces `n` at `d`. -/
theorem natCast_le_stableOffset_iff (hc : S.Covers p c) (hd : p.label d = ⊤) {n : ℕ} :
    (n : ℕ∞) ≤ S.stableOffset α hβ c p d ↔
      ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m),
        StageType.ForcesThreshold α hβ x.2.1 x.2.2 p d n ∧ S.ExtendsToCover c x := by
  rcases eq_or_ne n 0 with rfl | hn
  · refine ⟨fun _ ↦ ⟨⟨k, p, Function.Embedding.refl _⟩, ?_, c, rfl, hc⟩, fun _ ↦ by simp⟩
    exact StageType.forcesThreshold_zero (StageType.restrictFace_refl p) hd
  · rw [stableOffset, natCast_le_iSup_iff_of_ne_zero hn]
    simp only [natCast_le_iSup_iff_of_ne_zero hn, StageType.natCast_le_provisionalOffset_iff hn]
    exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, h, hx⟩, fun ⟨x, h, hx⟩ ↦ ⟨x, hx, h⟩⟩

/-- **The thresholds of the stable label**: if `c` covers the root `p` in `S` and `d` is labelled
the formal top in `p`, then the stable label is at least `β + n` exactly when some rooted cover of
`c` in `S` forces `n` at `d`. -/
theorem coe_add_le_stableLabel_iff (hc : S.Covers p c) (hd : p.label d = ⊤) {n : ℕ} :
    ((β + n : Ordinal.{u}) : Label.{u}) ≤ S.stableLabel α hβ c p d ↔
      ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m),
        StageType.ForcesThreshold α hβ x.2.1 x.2.2 p d n ∧ S.ExtendsToCover c x :=
  Label.coe_add_le_ofOffset_iff.trans (natCast_le_stableOffset_iff hc hd)

end Stable

/-! ### Normalization -/

section Normalization

variable {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}
  {t : StageType.{u} (blockStage (η + 1)) k} {c : Fin k → M}

/-- **Normalization of labels**, conditional on finite-extension receiving (from (R1), still to be
proved) and on forcing donors at `η` (still to be proved): at a cover `c` of `t` in `R`, the label
of a cell of `t` reducing to the formal top at `λ_η` is its stable label, computed in the reduction
of `R` to `λ_η` from the root `t↓λ_η`. -/
theorem label_eq_stableLabel (hR : R.IsConsistent) (hl : R.HasLegalTypes)
    (hrec : R.HasFiniteExtensionReceiving) (hF : ForcingDonors.{u} η) (hc : R.Covers t c)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) :
    t.label d = (R.reduce (isSuccPrelimit_blockStage η)).stableLabel (blockStage (η + 1))
      (isSuccPrelimit_blockStage η) c (t.reduce (isSuccPrelimit_blockStage η)) d :=
  Label.eq_of_forall_threshold_iff (t.label_mem_block hd).1 (t.label_mem_block hd).2
    Label.le_ofOffset Label.atStage_ofOffset fun n ↦
      (le_label_iff_exists_forcesThreshold hR hl hrec hF hc d hd n).trans
        (coe_add_le_stableLabel_iff (hc.reduce _) hd).symm

/-- **Determination by the reduction**, conditional on finite-extension receiving of both
realizations (from (R1), still to be proved) and on forcing donors at `η` (still to be proved): two
exactly consistent realizations at `λ_{η+1}` with legal types and equal reductions to `λ_η` are
equal.  No uniqueness or coherence of expansions is assumed. -/
theorem eq_of_reduce_eq_of_forcingDonors (hF : ForcingDonors.{u} η)
    {R' : Realization.{u, v} (blockStage (η + 1)) M} (hR : R.IsConsistent)
    (hR' : R'.IsConsistent) (hl : R.HasLegalTypes) (hl' : R'.HasLegalTypes)
    (hrec : R.HasFiniteExtensionReceiving) (hrec' : R'.HasFiniteExtensionReceiving)
    (h : R.reduce (isSuccPrelimit_blockStage η) = R'.reduce (isSuccPrelimit_blockStage η)) :
    R = R' := by
  refine Realization.ext fun u ↦ ?_
  have hu : (R.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) =
      (R'.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) := by
    rw [← reduce_eval, ← reduce_eval, h]
  cases ht : R.eval u with
  | none =>
    rw [ht, Option.map_none] at hu
    exact (Option.map_eq_none_iff.mp hu.symm).symm
  | some t =>
    rw [ht, Option.map_some] at hu
    obtain ⟨t', ht', htt'⟩ := Option.map_eq_some_iff.mp hu.symm
    rw [ht']
    refine congrArg some (StageType.eq_of_reduce_eq_of_threshold_iff htt'.symm
      fun i j hij hi n ↦ ?_)
    have hj : (t'.reduce (isSuccPrelimit_blockStage η)).label j = ⊤ :=
      (StageType.label_congr htt'.symm hij).symm.trans hi
    rw [label_eq_stableLabel hR hl hrec hF (covers_of_eval u ht) i hi,
      label_eq_stableLabel hR' hl' hrec' hF (covers_of_eval u ht') j hj, h,
      stableLabel_congr htt'.symm hij]

end Normalization

end Realization

end VaughtConjecture

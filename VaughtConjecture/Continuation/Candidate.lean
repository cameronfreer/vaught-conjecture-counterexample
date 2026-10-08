/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Label.Transform
import VaughtConjecture.Realization.BlockStages
import VaughtConjecture.Realization.Hull
import VaughtConjecture.Realization.Model
import VaughtConjecture.Stage.Threshold

/-!
# The stable candidate at the next block

Roadmap, Layer 4, output 1 of higher-stage reconstruction (the structural candidate: lawfulness,
exact partial evaluation and literal reduct, before modelhood); semantic contract, item 7.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`, and
`λ_{ξ+1} = blockStage (ξ + 1)` is the next block stage (`= λ_ξ + ω`, by `blockStage_add_one`).
Stable offsets and stable labels (`Realization.stableOffset`, `Realization.stableLabel`, in
`VaughtConjecture.Continuation.Normalization`) are those of `R` itself, read at `λ_{ξ+1}`.

**The stable section and the stable candidate.**  At a typed tuple `u` of type `t`, the **stable
section** (`Realization.stableSection`) keeps every label of `t` below `λ_ξ` and puts the stable
label at every cell labelled the formal top.  `R` is **stably lawful**
(`Realization.IsStablyLawful`) when the stable section is a lawful section of the rows of `t` at
every typed tuple.  Given that, the **stable type** (`Realization.stableType`) is the stage type at
`λ_{ξ+1}` on the scheme of `t` with the stable section as labels, and the **stable candidate**
(`Realization.stableCandidate`) is the realization at `λ_{ξ+1}` that evaluates a tuple to its
stable type when `R` types it and is undefined otherwise
(`Realization.stableCandidate_eval_isSome_iff`).  Lawfulness is an argument of the definition,
because a stage type carries the lawfulness of its labels.

**Structural properties** (no model is used):

* **reduction** (`Realization.stableCandidate_reduce`), unconditional: the reduction of the
  candidate to `λ_ξ` is `R`, since a stable label is at least `λ_ξ`;
* **legality** and **covering** (`Realization.hasLegalTypes_stableCandidate`,
  `Realization.isCovering_stableCandidate`): those of `R`, since the candidate has the schemes of
  `R` and the same typed tuples;
* **exact consistency** (`Realization.isConsistent_stableCandidate`) from the exact consistency
  **and the covering** of `R`.  Undefined faces agree because the schemes agree; the labels need the
  face compatibility of stable offsets (`Realization.stableOffset_comap`), in which covering
  places a rooted cover of a face and the tuple itself in one occurrence
  (`Realization.exists_occurrence_forcesThreshold`).

**Lawfulness, law by law.**  Fix a typed tuple `u` of type `t`.

* **Order** (`Realization.orderly_stableSection`), unconditional: the trivial rooted cover forces
  the grade of a cell labelled the formal top, so its stable label is `λ_ξ + i` with `i` at least
  the grade, or the formal top (`Realization.stableSection_eq_top_or_exists`).
* **Locality** (`Realization.locality_stableSection`), from exact consistency and covering.  Let
  `k` be the arity of `u`, choose `N > k` above every finite stable offset at `u`, and take, by
  covering, one occurrence `z` containing `u` that attains every finite stable offset and forces
  `N` at the cells with stable label `⊤`.  For each cell `d` labelled the formal top, a lift of the
  type of `z` to `λ_ξ + ω` has, at `d`, exactly the label of the provisional offset there
  (`StageType.exists_lift_label_eq_ofOffset`); its face along the coordinates of `u` is a lawful
  section of the rows of `t`.  The stable section is the **collapse** above `λ_ξ + N`
  (`Label.collapse`) of the pointwise minimum of these finitely many lawful sections
  (`Realization.exists_isLawful_collapse_inf'`); locality follows from `Label.TransformsTo.inf`
  and `Label.TransformsTo.collapse`.
* **Availability** holds whenever the stable section at the first cell is a label of `t` below
  `λ_ξ`.  At a first cell `s₀` labelled the formal top, availability for the pair `(s₀, t₀)` is
  exactly the transfer of every threshold forced at `s₀` over a realized rooted cover to some
  cell labelled the formal top at the graded index of `t₀`, over a realized rooted cover
  (`Realization.availability_stableSection_iff`, with no hypothesis on `R`).  When that graded
  index carries at most one cell labelled the formal top, every lift carries there a label at
  least the one at `s₀` (`Realization.availability_stableSection_of_injOn`, unconditional).  Two or
  more cells labelled the formal top at one graded index are **twins**; there the pointwise
  minimum of two lawful lifts need not satisfy availability (the stage-type example of
  `VaughtConjecture.Stage.ThresholdExamples`, on an incomplete scheme).  **Availability at twins
  is proved from legal types** (`Realization.availability_stableSection_of_hasLegalTypes`): a legal
  rooted cover `(q, f)` forcing `N` at `s₀` forces `N`, over the same cover, at a cell labelled the
  formal top at the graded index of `t₀` (`StageType.exists_forcesThreshold_twin_face`, in
  `VaughtConjecture.Stage.Threshold`).  The capped lift of `q` at `λ_ξ + K`, for `K` the largest
  grade of a cell of `q` labelled the formal top, gives `N ≤ K`; completeness and availability of
  `q` give a cell `D` of full scope and grade `K` labelled the formal top; availability of the row
  of `D`, which is lawful below `D` by consistency of the rows, names a cell `w` at the graded
  index of `t₀` with the row of `D` at least as large at `w` as at `s₀`; and locality of every
  lift at `D` gives the label of `w` at least the minimum of those of `s₀` and `D`, both at least
  `λ_ξ + N`.

Hence every exactly consistent covering realization with legal types is stably lawful
(`Realization.isStablyLawful_of_hasLegalTypes`), in particular every model
(`Realization.IsModel.isStablyLawful`).  A realization is also stably lawful under exact
consistency and covering, without legal types, when no type has twins
(`Realization.isStablyLawful_of_injOn_gradedIndex`), and with no hypothesis at all when it is
cover-hollow (`Realization.isStablyLawful_of_isCoverHollow`).  Unbounded top-grade growth and
non-hollowness are not used for lawfulness; they concern receiving of the candidate, below.

**Two hypotheses on single types are refuted** (negative special cases).  Two finite statements
about stage types that would give availability at twins through every lift are false; they are
defined, and refuted, only in `VaughtConjecture.Continuation.CandidateCounterexamples`.

* **Synchronizing cofaces** would transfer forcing from a cell `a` to a cell `b` at a graded index
  with twins: for a legal stage type `q` and cells `a`, `b` labelled the formal top with the scope
  of `a` in that of `b` and equal grades, a scheme `S` on one more point carrying a legal coface of
  `q` such that every lawful section of the rows of `S` is at least as large at `b` as at `a`, to
  be realized over an occurrence by generalized saturation.  This is false at every block stage
  (`Continuation.CandidateCounterexamples.not_synchronizingCofaces_blockStage`); its form without
  the requirement that `a` and `b` be labelled the formal top and its form restricted to lifts of
  members of the coface family are false at `ω` (same file; the first is proved in universe `0`).
  The reason is bountifulness: the scheme of a legal coface extends every lawful section of the
  rows of `q`, so no coface orders two cells of `q` that some lift of `q` orders the other way.
  The special case is two cells labelled the formal top at one graded index of `onePointScheme 2`,
  with the lift `(ω + 1, ω + 2)`.
* **Twin ordering** (`Continuation.CandidateCounterexamples.TwinOrdering`) would give availability
  directly: for a legal stage type `q` and cells `s₀`, `t₀` labelled the formal top with the scope
  of `s₀` strictly inside that of `t₀` and equal grades, one cell labelled the formal top at the
  graded index of `t₀` that is at least as large as `s₀` in every lift of `q`.  It is false at
  every stage that is zero or a limit, in particular at every block stage
  (`Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`).  The special case is a
  legal scheme on two points with five cells: `s₀` of scope `{0}` and grade `1`, a cell of scope
  `{1}` and grade `1`, two twins of full scope and grade `1`, and a cell of full scope and grade
  `2`.  On its type every lift sets `s₀` to the larger twin, and both orders of the twins occur.

So no hypothesis that orders a twin above `s₀` in all lifts of a single type can hold.  The
transfer that does hold happens inside the forcing cover: it carries a level forced at `s₀` over a
legal cover to a twin over the same cover, and per-lift statements ignore the forced level.  On
the five-cell type the forced level at `s₀` is its grade `1`: it is at least the grade by the order
law, and at most `1` because every cell labelled the formal top has grade `1`, so the capped lift
with `K = 1` is a lift of the type (`StageType.capLift_reduce`).  Every twin also has level `1` by
the order law, while lifts still order the twins both ways above level `1`.

**The cases.**

* **Cover-hollow** `R`: every stable label at a cell labelled the formal top is `⊤`, the stable
  section is the label section, and the candidate is `R` read at `λ_{ξ+1}`
  (`Realization.stableCandidate_eval_of_isCoverHollow`).  It has no label in `[λ_ξ, λ_ξ + ω)`, so
  it is not a model (`Realization.not_isModel_stableCandidate_of_isCoverHollow`): uniformity at
  `γ = λ_ξ` fails.
* **Bounded stable labels**: if every stable label is at most `λ_ξ + K`, the candidate is not a
  model (`Realization.not_isModel_stableCandidate_of_stableLabel_le`): high-arity dominance at
  `γ = λ_ξ + K` fails.  Bounded top-grade growth is expected to give such a bound; that bound is
  not proved here.
* **A model expansion**: if `R` is the reduction of an exactly consistent realization at `λ_{ξ+1}`
  with legal types and finite-extension receiving, given forcing donors at `ξ`, the stable section
  is the label section of that realization (normalization, `Realization.label_eq_stableLabel`), so
  `R` is stably lawful (`Realization.isStablyLawful_of_reduce_eq`).  Finite-extension receiving
  follows from (R1) of the table of Layer 3, and forcing donors are compiled in this repository
  (theorem named) at every block index (`forcingDonors_blockStage`).

**Relation to the roadmap.**  The roadmap builds the structural candidate "from consistency and
covering" (Layer 4, output 1).  Here the order law, locality, exact partial evaluation, the
reduction, legality, covering and exact consistency need no more; availability needs, in
addition, legal types (or the absence of twins).  The splice of two witnesses (roadmap, Layer
3; compiled in a general form, `Label.TransformsTo.splice_bandMap`) is not used: locality comes
from pointwise minima and collapse.

**What is not claimed.**  The candidate is not claimed to be a model, and output 3 is not proved.
Its modelhood is to follow from the cap-to-model theorem at `λ_{ξ+1}`
(`Realization.isModel_of_hasFiniteCutReceiving`), and needs: finite-cut receiving of the
candidate over positive roots, which is (R4) of the table of Layer 3 (stable capped receiving,
for a model with non-hollow unbounded top-grade growth; still to be proved); the empty root,
through the coatom extension at `λ_{ξ+1}` over the empty face; and the plain and apex coatom
extension properties at `λ_{ξ+1}` (`StageType.HasCoatomExtensions` and
`StageType.HasApexCoatomExtensions` at `blockStage (ξ + 1)`) for the uniformity and dominance
instances.  None of these is stated here.  The argument `hlaw` of the definition, the stable
lawfulness of `R`, is supplied for every model by `Realization.IsModel.isStablyLawful`.  No (R1),
forcing donors, normalization or uniqueness of expansions is used except in the last case above.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Ordinal StageType

/-! ### Auxiliary facts -/

/-- `β + n < β + N` as labels for `n < N`. -/
private theorem coe_add_lt_coe_add (β : Ordinal.{u}) {n N : ℕ} (h : n < N) :
    ((β + n : Ordinal.{u}) : Label.{u}) < ((β + N : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (add_lt_add_right (Nat.cast_lt.mpr h) β))

/-- A lift of a stage type `t` to a larger stage gives a lawful section of the rows of `t`, with
the labels of the lift at the same positions, each reducing to the label of `t`. -/
private theorem exists_isLawful_of_reduce_eq {β γ : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β}
    {k : ℕ} {t : StageType.{u} β k} {P : StageType.{u} γ k} (hP : P.reduce hβ = t) :
    ∃ ℓ : Fin t.card → Label.{u}, t.rows.IsLawful ℓ ∧ t.card = P.card ∧
      (∀ (i : Fin t.card) (j : Fin P.card), (i : ℕ) = j → ℓ i = P.label j) ∧
      ∀ i, Label.reduce β (ℓ i) = t.label i := by
  obtain ⟨S, ℓ, hw, hc, hl, hat⟩ := P
  have hS : S = t.toScheme := congrArg StageType.toScheme hP
  subst hS
  exact ⟨ℓ, hl, rfl, fun i j hij ↦ by rw [Fin.ext hij], fun i ↦ label_congr hP rfl⟩

namespace Realization

variable {M : Type v} {k : ℕ}

/-! ### Rooted covers in one occurrence -/

section Rooted

variable {α β : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β} {S : Realization.{u, v} β M}

/-- For a positive `n`, `n` is at most the stable offset exactly when some rooted cover forces it;
no hypothesis is needed. -/
private theorem natCast_le_stableOffset_iff_of_ne_zero {c : Fin k → M} {p : StageType.{u} β k}
    {d : Fin p.card} {n : ℕ} (hn : n ≠ 0) :
    (n : ℕ∞) ≤ S.stableOffset α hβ c p d ↔
      ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m),
        StageType.ForcesThreshold α hβ x.2.1 x.2.2 p d n ∧ S.ExtendsToCover c x := by
  rw [stableOffset, natCast_le_iSup_iff_of_ne_zero hn]
  simp only [natCast_le_iSup_iff_of_ne_zero hn, StageType.natCast_le_provisionalOffset_iff hn]
  exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, h, hx⟩, fun ⟨x, h, hx⟩ ↦ ⟨x, hx, h⟩⟩

/-- **Rooted covers in one occurrence**: under exact consistency and covering, finitely many rooted
covers of the face `f.trans u` of a typed tuple `u`, each forcing a threshold at a cell of a root
`p`, are dominated by one occurrence `z` containing `u` along `b`: the type of `z` restricts to
the type of `u` along `b`, and `(z.type, f.trans b)` forces every one of the thresholds. -/
theorem exists_occurrence_forcesThreshold (hS : S.IsConsistent) (hc : S.IsCovering)
    {u : Fin k ↪ M} {t : StageType.{u} β k} (ht : S.eval u = some t) {k' : ℕ}
    (f : Fin k' ↪ Fin k) {p : StageType.{u} β k'} {ι : Type*} [Finite ι] (d : ι → Fin p.card)
    (T : ι → ℕ) (h : ∀ j, ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k' ↪ Fin m),
      StageType.ForcesThreshold α hβ x.2.1 x.2.2 p (d j) (T j) ∧ S.ExtendsToCover (f.trans u) x) :
    ∃ (z : S.Occurrence) (b : Fin k ↪ Fin z.arity), b.trans z.tuple = u ∧
      restrictFace b z.type = some t ∧
      ∀ j, StageType.ForcesThreshold α hβ z.type (f.trans b) p (d j) (T j) := by
  classical
  have := Fintype.ofFinite ι
  choose x hx using h
  choose s hs hcs using fun j ↦ (hx j).2
  obtain ⟨z, hz⟩ := hc.exists_subset_support (univ.map u ∪ univ.biUnion fun j ↦ univ.image (s j))
  obtain ⟨b, hb⟩ := z.exists_trans_eq (subset_union_left.trans hz)
  refine ⟨z, b, hb, by rw [← hS z.tuple z.type b z.eval_tuple, hb, ht], fun j ↦ ?_⟩
  obtain ⟨a, ha⟩ := z.exists_trans_eq (t := ⟨s j, (hcs j).injective⟩) fun y hy ↦
    hz (mem_union_right _ (mem_biUnion.mpr ⟨j, mem_univ _, by simpa using hy⟩))
  have hqa : restrictFace a z.type = some (x j).2.1 := by
    rw [← hS z.tuple z.type a z.eval_tuple, ha]
    exact (hcs j).eval_eq
  have hga : (x j).2.2.trans a = f.trans b := by
    ext i
    refine congrArg Fin.val (z.tuple.injective ?_)
    have h₁ := DFunLike.congr_fun ha ((x j).2.2 i)
    have h₂ := DFunLike.congr_fun hb (f i)
    have h₃ := congrFun (hs j) i
    simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      Function.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  have h' := (hx j).1.trans_face hqa
  rwa [hga] at h'

/-- **Stable offsets along faces of a typed tuple**, from exact consistency and covering: at the
face of `u` along a closed face `f` of its type, the stable offset of a cell of the restricted type
is the stable offset of the transported cell at `u`.  Cells are matched by position. -/
theorem stableOffset_comap (hS : S.IsConsistent) (hc : S.IsCovering) {u : Fin k ↪ M}
    {t : StageType.{u} β k} (ht : S.eval u = some t) {j : ℕ} (f : Fin j ↪ Fin k)
    (hf : univ.map f ∈ t.toCellScheme.faces) (i : Fin (t.comap f hf).card) :
    S.stableOffset α hβ (f.trans u) (t.comap f hf) i = S.stableOffset α hβ u t (t.cellMap f i) := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [natCast_le_stableOffset_iff_of_ne_zero hn, natCast_le_stableOffset_iff_of_ne_zero hn]
  refine ⟨fun ⟨x, hx, hcov⟩ ↦ ?_, fun ⟨x, hx, s, hs, hcs⟩ ↦ ?_⟩
  · obtain ⟨z, b, hb, hzt, hz⟩ := exists_occurrence_forcesThreshold hS hc ht f (ι := Unit)
      (fun _ ↦ i) (fun _ ↦ n) fun _ ↦ ⟨x, hx, hcov⟩
    exact ⟨⟨z.arity, z.type, b⟩, (ForcesThreshold.trans_comap_iff hzt hf i).mp (hz ()), z.tuple,
      congrArg DFunLike.coe hb, covers_of_eval _ z.eval_tuple⟩
  · refine ⟨⟨x.1, x.2.1, f.trans x.2.2⟩, (ForcesThreshold.trans_comap_iff hx.1 hf i).mpr hx, s, ?_,
      hcs⟩
    funext y
    exact congrFun hs (f y)

/-- The stable section of a typed tuple as a collapse of a pointwise minimum of lawful sections,
at a general pair of stages `β` and `β + ω`. -/
private theorem exists_isLawful_collapse_inf'_aux (hS : S.IsConsistent) (hc : S.IsCovering)
    {u : Fin k ↪ M} {t : StageType.{u} β k} (ht : S.eval u = some t)
    (hD : (univ.filter fun d ↦ t.label d = ⊤).Nonempty) :
    ∃ (N : ℕ) (ℓ : Fin t.card → Fin t.card → Label.{u}), (∀ j, t.rows.IsLawful (ℓ j)) ∧ k < N ∧
      ∀ e, (if t.label e = ⊤ then S.stableLabel (β + ω) hβ u t e else t.label e) =
        Label.collapse β N ((univ.filter fun d ↦ t.label d = ⊤).inf' hD fun j ↦ ℓ j e) := by
  classical
  set D := univ.filter fun d ↦ t.label d = ⊤
  have hcov : S.Covers t u := covers_of_eval u ht
  set o : Fin t.card → ℕ∞ := fun d ↦ S.stableOffset (β + ω) hβ u t d
  set N : ℕ := k + 1 + univ.sup fun d ↦ (o d).toNat
  set T : Fin t.card → ℕ := fun d ↦ if o d = ⊤ then N else (o d).toNat
  have hlt : ∀ d, (o d).toNat < N := fun d ↦
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (by
      have := le_sup (f := fun d ↦ (o d).toNat) (mem_univ d)
      omega)
  have hT : ∀ d, (T d : ℕ∞) ≤ o d := fun d ↦ by
    by_cases h : o d = ⊤
    · rw [h]; exact le_top
    · simp only [T, h, ↓reduceIte, ENat.natCast_toNat h, le_rfl]
  obtain ⟨z, b, hb, hzt, hforce⟩ := exists_occurrence_forcesThreshold hS hc ht
    (Function.Embedding.refl _) (ι := D) (fun j ↦ j.1) (fun j ↦ T j.1) fun j ↦ by
      simpa only [Function.Embedding.refl_trans] using
        (natCast_le_stableOffset_iff hcov (mem_filter.mp j.2).2).mp (hT j.1)
  simp only [Function.Embedding.refl_trans] at hforce
  set π : Fin t.card → ℕ∞ := fun d ↦ provisionalOffset (β + ω) hβ z.type b t d
  have hπo : ∀ d, π d ≤ o d := fun d ↦
    le_iSup₂ (f := fun x (_ : S.ExtendsToCover u x) ↦ provisionalOffset (β + ω) hβ x.2.1 x.2.2 t d)
      (⟨z.arity, z.type, b⟩ : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m))
      ⟨z.tuple, congrArg DFunLike.coe hb, covers_of_eval _ z.eval_tuple⟩
  have hlift : ∀ j : Fin t.card, ∃ ℓ : Fin t.card → Label.{u}, t.rows.IsLawful ℓ ∧
      (t.label j = ⊤ → (∀ e, t.label e ≠ ⊤ → ℓ e = t.label e) ∧
        (∀ e (he : e ∈ D), ((β + T e : Ordinal.{u}) : Label.{u}) ≤ ℓ e) ∧
        ℓ j = Label.ofOffset β (π j)) := fun j ↦ by
    by_cases hj : t.label j = ⊤
    · obtain ⟨Q, hQ, P, hP, hPj⟩ := exists_lift_label_eq_ofOffset (hβ := hβ) hzt hj
      obtain ⟨P', hP', hP't⟩ := exists_restrictFace_reduce_eq hzt hQ
      obtain rfl : P = P' := Option.some_injective _ (hP.symm.trans hP')
      obtain ⟨ℓ, hℓ, hcard, hℓP, hℓt⟩ := exists_isLawful_of_reduce_eq hP't
      refine ⟨ℓ, hℓ, fun _ ↦ ⟨fun e he ↦ ?_, fun e he ↦ ?_, ?_⟩⟩
      · have hlt : Label.reduce β (ℓ e) < β := (hℓt e).symm ▸ (t.atStage e).resolve_right he
        rw [← hℓt e]
        exact (Label.reduce_of_lt (Label.reduce_lt_iff.mp hlt)).symm
      · rw [hℓP e (Fin.cast hcard e) rfl]
        exact (hforce ⟨e, he⟩).2 Q P hQ hP _ rfl
      · rw [hℓP j (Fin.cast hcard j) rfl]
        exact hPj _ rfl
    · exact ⟨t.label, t.isLawful, fun h ↦ absurd h hj⟩
  choose ℓ hℓ using hlift
  have hge : ∀ e (he : e ∈ D), ((β + T e : Ordinal.{u}) : Label.{u}) ≤ D.inf' hD fun j ↦ ℓ j e :=
    fun e he ↦ le_inf' hD _ fun j hj ↦ ((hℓ j).2 (mem_filter.mp hj).2).2.1 e he
  refine ⟨N, ℓ, fun j ↦ (hℓ j).1, by omega, fun e ↦ ?_⟩
  by_cases he : t.label e = ⊤
  · have heD : e ∈ D := mem_filter.mpr ⟨mem_univ _, he⟩
    rw [ite_eq_left he, stableLabel]
    -- the stable label is the label of the stable offset
    change Label.ofOffset β (o e) = _
    by_cases hoe : o e = ⊤
    · have hTe : T e = N := ite_eq_left hoe
      rw [hoe, Label.ofOffset_top]
      exact (Label.reduce_of_le (hTe ▸ hge e heD)).symm
    · have hTe : T e = (o e).toNat := ite_eq_right hoe
      have hπe : π e = o e := le_antisymm (hπo e) (by
        rw [← ENat.natCast_toNat hoe, ← hTe]
        exact (hforce ⟨e, heD⟩).le_provisionalOffset)
      have hinf : (D.inf' hD fun j ↦ ℓ j e) = ((β + (o e).toNat : Ordinal.{u}) : Label.{u}) :=
        le_antisymm ((inf'_le _ heD).trans_eq (by
          rw [((hℓ e).2 he).2.2, hπe, ← ENat.natCast_toNat hoe, Label.ofOffset_natCast,
            ENat.toNat_natCast])) (hTe ▸ hge e heD)
      rw [hinf, Label.collapse, Label.reduce_of_lt (coe_add_lt_coe_add β (hlt e)),
        ← ENat.natCast_toNat hoe, Label.ofOffset_natCast, ENat.toNat_natCast]
  · obtain ⟨j₀, hj₀⟩ := hD
    have hinf : (D.inf' ⟨j₀, hj₀⟩ fun j ↦ ℓ j e) = t.label e :=
      le_antisymm ((inf'_le _ hj₀).trans_eq (((hℓ j₀).2 (mem_filter.mp hj₀).2).1 e he))
        (le_inf' _ _ fun j hj ↦ (((hℓ j).2 (mem_filter.mp hj).2).1 e he).ge)
    rw [ite_eq_right he, hinf, Label.collapse,
      Label.reduce_of_lt (((t.atStage e).resolve_right he).trans_le (Label.coe_le_coe_add β N))]

end Rooted

/-! ### The stable section -/

variable {ξ : Ordinal.{u}}

section Definitions

variable (R : Realization.{u, v} (blockStage ξ) M)

/-- The **stable section** at a typed tuple `u` of type `t`: the label of `t` at a cell below
`λ_ξ`, and the stable label at a cell labelled the formal top. -/
noncomputable def stableSection (u : Fin k ↪ M) (t : StageType.{u} (blockStage ξ) k) :
    Fin t.card → Label.{u} := fun d ↦
  if t.label d = ⊤ then
    R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d
  else t.label d

/-- `R` is **stably lawful**: at every typed tuple, the stable section is a lawful section of the
rows of its type. -/
def IsStablyLawful : Prop :=
  ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
    t.rows.IsLawful (R.stableSection u t)

end Definitions

variable {R : Realization.{u, v} (blockStage ξ) M} {u : Fin k ↪ M}
  {t : StageType.{u} (blockStage ξ) k} {d : Fin t.card}

/-- At a cell labelled the formal top, the stable section is the stable label. -/
theorem stableSection_of_eq_top (hd : t.label d = ⊤) :
    R.stableSection u t d =
      R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d :=
  ite_eq_left hd

/-- At any other cell, the stable section is the label of `t`. -/
theorem stableSection_of_ne_top (hd : t.label d ≠ ⊤) : R.stableSection u t d = t.label d :=
  ite_eq_right hd

/-- **The order-law lower bound**: at a cell labelled the formal top, the stable offset is at
least the grade (the trivial rooted cover). -/
theorem grade_le_stableOffset (ht : R.eval u = some t) (hd : t.label d = ⊤) :
    (t.toCellScheme.grade d : ℕ∞) ≤
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d :=
  (natCast_le_stableOffset_iff (covers_of_eval u ht) hd).mpr
    ⟨⟨k, t, Function.Embedding.refl _⟩, forcesThreshold_of_le_grade (restrictFace_refl t) hd le_rfl,
      u, rfl, covers_of_eval u ht⟩

/-- At a cell labelled the formal top, the stable section is the formal top or `λ_ξ + i` with `i`
at least the grade of the cell. -/
theorem stableSection_eq_top_or_exists (ht : R.eval u = some t) (hd : t.label d = ⊤) :
    R.stableSection u t d = ⊤ ∨ ∃ i : ℕ, t.toCellScheme.grade d ≤ i ∧
      R.stableSection u t d = ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) := by
  have hg := grade_le_stableOffset ht hd
  rw [stableSection_of_eq_top hd, stableLabel]
  induction h : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d
    using ENat.recTopCoe with
  | top => exact Or.inl Label.ofOffset_top
  | coe i => exact Or.inr ⟨i, Nat.cast_le.mp (h ▸ hg), Label.ofOffset_natCast i⟩

/-- The stable section is a label at the stage `λ_{ξ+1}`. -/
theorem atStage_stableSection (d : Fin t.card) :
    Label.AtStage (blockStage (ξ + 1)) (R.stableSection u t d) := by
  by_cases hd : t.label d = ⊤
  · rw [stableSection_of_eq_top hd, blockStage_add_one]
    exact Label.atStage_ofOffset
  · rw [stableSection_of_ne_top hd]
    exact (t.atStage d).mono (blockStage_lt_blockStage_add_one ξ).le

/-- The stable section reduces at `λ_ξ` to the label of `t`. -/
theorem reduce_stableSection (d : Fin t.card) :
    Label.reduce (blockStage ξ) (R.stableSection u t d) = t.label d := by
  by_cases hd : t.label d = ⊤
  · rw [stableSection_of_eq_top hd, hd]
    exact Label.reduce_of_le Label.le_ofOffset
  · rw [stableSection_of_ne_top hd]
    exact (t.atStage d).reduce_eq

/-- Below a cell whose label is not the formal top, the stable section is monotone in the labels
of `t`. -/
theorem stableSection_le_of_ne_top {d e : Fin t.card} (hd : t.label d ≠ ⊤)
    (h : t.label d ≤ t.label e) : R.stableSection u t d ≤ R.stableSection u t e := by
  rw [stableSection_of_ne_top hd]
  by_cases he : t.label e = ⊤
  · rw [stableSection_of_eq_top he]
    exact ((t.atStage d).resolve_right hd).le.trans Label.le_ofOffset
  · rwa [stableSection_of_ne_top he]

/-! ### The stable type and the stable candidate -/

section Candidate

variable (R) (hlaw : R.IsStablyLawful)

/-- The **stable type** at a typed tuple `u` of type `t`: the stage type at `λ_{ξ+1}` on the
scheme of `t` with the stable section as labels. -/
noncomputable def stableType (u : Fin k ↪ M) (t : StageType.{u} (blockStage ξ) k)
    (h : R.eval u = some t) : StageType.{u} (blockStage (ξ + 1)) k where
  toScheme := t.toScheme
  label := R.stableSection u t
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := hlaw u t h
  atStage := atStage_stableSection

/-- The **stable candidate**: the realization at `λ_{ξ+1}` that evaluates a tuple typed in `R` to
its stable type and is undefined at the tuples untyped in `R`. -/
noncomputable def stableCandidate : Realization.{u, v} (blockStage (ξ + 1)) M where
  eval u := (R.eval u).pmap (R.stableType hlaw u) fun _ h ↦ h

variable {R hlaw}

/-- The scheme of the stable type is the scheme of `t`. -/
@[simp] theorem stableType_toScheme (h : R.eval u = some t) :
    (R.stableType hlaw u t h).toScheme = t.toScheme :=
  rfl

/-- The labels of the stable type are the stable section. -/
@[simp] theorem stableType_label (h : R.eval u = some t) (d : Fin t.card) :
    (R.stableType hlaw u t h).label d = R.stableSection u t d :=
  rfl

/-- The stable type reduces at `λ_ξ` to `t`. -/
theorem reduce_stableType (h : R.eval u = some t) :
    (R.stableType hlaw u t h).reduce (isSuccPrelimit_blockStage ξ) = t :=
  StageType.ext rfl fun i j hij ↦ by
    rw [Fin.ext hij]
    exact reduce_stableSection j

/-- At a typed tuple the candidate evaluates to the stable type. -/
theorem stableCandidate_eval_of_eval (h : R.eval u = some t) :
    (R.stableCandidate hlaw).eval u = some (R.stableType hlaw u t h) :=
  Option.pmap_eq_some_iff.mpr ⟨t, h, h, rfl⟩

/-- Every value of the candidate is a stable type. -/
theorem exists_eq_stableType_of_stableCandidate_eval
    {P : StageType.{u} (blockStage (ξ + 1)) k} (h : (R.stableCandidate hlaw).eval u = some P) :
    ∃ (t : StageType.{u} (blockStage ξ) k) (ht : R.eval u = some t),
      P = R.stableType hlaw u t ht := by
  obtain ⟨t, ht, -, rfl⟩ := Option.pmap_eq_some_iff.mp h
  exact ⟨t, ht, rfl⟩

/-- The candidate is undefined exactly at the tuples untyped in `R`. -/
theorem stableCandidate_eval_eq_none_iff :
    (R.stableCandidate hlaw).eval u = none ↔ R.eval u = none :=
  Option.pmap_eq_none_iff

/-- **Exact partial evaluation**: the candidate types exactly the tuples typed in `R`. -/
theorem stableCandidate_eval_isSome_iff :
    ((R.stableCandidate hlaw).eval u).isSome ↔ (R.eval u).isSome := by
  simp [stableCandidate]

/-- **Reduction**, unconditional: the reduction of the candidate to `λ_ξ` is `R`. -/
theorem stableCandidate_reduce :
    (R.stableCandidate hlaw).reduce (isSuccPrelimit_blockStage ξ) = R := by
  refine Realization.ext fun u ↦ ?_
  rw [reduce_eval]
  cases h : R.eval u with
  | none => rw [stableCandidate_eval_eq_none_iff.mpr h, Option.map_none]
  | some t => rw [stableCandidate_eval_of_eval h, Option.map_some, reduce_stableType]

/-- **Legality**: the candidate has legal types when `R` does; legality depends only on the
scheme. -/
theorem hasLegalTypes_stableCandidate (hl : R.HasLegalTypes) :
    (R.stableCandidate hlaw).HasLegalTypes := fun _ u P hP ↦ by
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hP
  exact hl u t ht

/-- **Covering**: the candidate is covering when `R` is. -/
theorem isCovering_stableCandidate (hc : R.IsCovering) : (R.stableCandidate hlaw).IsCovering :=
  fun _ u ↦ by
    obtain ⟨m, w, f, hf, hw⟩ := hc u
    exact ⟨m, w, f, hf, stableCandidate_eval_isSome_iff.mpr hw⟩

/-- **Exact consistency** of the candidate, from the exact consistency and the covering of `R`:
undefined faces agree because the schemes agree, and the labels by `stableOffset_comap`. -/
theorem isConsistent_stableCandidate (hR : R.IsConsistent) (hc : R.IsCovering) :
    (R.stableCandidate hlaw).IsConsistent := fun _ _ w P g hP ↦ by
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hP
  by_cases hf : univ.map g ∈ t.toCellScheme.faces
  · have hg : R.eval (g.trans w) = some (t.comap g hf) := (hR w t g ht).trans
      (restrictFace_of_mem t g hf)
    rw [stableCandidate_eval_of_eval hg, restrictFace_of_mem (R.stableType hlaw w t ht) g hf]
    refine congrArg some (StageType.ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    -- the labels of the two stable types are the stable sections
    change R.stableSection (g.trans w) (t.comap g hf) i = R.stableSection w t (t.cellMap g i)
    by_cases h : t.label (t.cellMap g i) = ⊤
    · rw [stableSection_of_eq_top (t := t.comap g hf) (d := i) h, stableSection_of_eq_top h]
      exact congrArg (Label.ofOffset _) (stableOffset_comap hR hc ht g hf i)
    · rw [stableSection_of_ne_top (t := t.comap g hf) (d := i) h, stableSection_of_ne_top h]
      rfl
  · rw [restrictFace_of_notMem (R.stableType hlaw w t ht) g hf, stableCandidate_eval_eq_none_iff,
      hR w t g ht, restrictFace_of_notMem t g hf]

end Candidate

/-! ### Lawfulness: the order law and locality -/

/-- **The order law** of the stable section, unconditional. -/
theorem orderly_stableSection (ht : R.eval u = some t) (d : Fin t.card) :
    Label.IsSelfVisible (t.toCellScheme.grade d) (R.stableSection u t d) := by
  by_cases hd : t.label d = ⊤
  · rcases stableSection_eq_top_or_exists ht hd with h | ⟨i, hi, h⟩ <;> rw [h]
    · exact Label.isSelfVisible_top _
    · exact Label.isSelfVisible_coe_add (isSuccPrelimit_blockStage ξ) hi
  · rw [stableSection_of_ne_top hd]
    exact t.isLawful.orderly d

/-- **The stable section as a collapse of a pointwise minimum of lawful sections**, from exact
consistency and covering: when some cell of `t` is labelled the formal top, there are lawful
sections `ℓ j` of the rows of `t`, one for each such cell `j`, and `N` above the arity, such that
the stable section is the collapse above `λ_ξ + N` of their pointwise minimum.  The sections are
the faces at `u` of lifts of the type of one occurrence attaining all stable offsets at `u`. -/
theorem exists_isLawful_collapse_inf' (hR : R.IsConsistent) (hc : R.IsCovering)
    (ht : R.eval u = some t) (hD : (univ.filter fun d ↦ t.label d = ⊤).Nonempty) :
    ∃ (N : ℕ) (ℓ : Fin t.card → Fin t.card → Label.{u}), (∀ j, t.rows.IsLawful (ℓ j)) ∧ k < N ∧
      ∀ e, R.stableSection u t e = Label.collapse (blockStage ξ) N
        ((univ.filter fun d ↦ t.label d = ⊤).inf' hD fun j ↦ ℓ j e) := by
  obtain ⟨N, ℓ, hℓ, hkN, h⟩ := exists_isLawful_collapse_inf'_aux hR hc ht hD
  refine ⟨N, ℓ, hℓ, hkN, fun e ↦ ?_⟩
  rw [← h e, stableSection, blockStage_add_one]

/-- **Locality** of the stable section, from exact consistency and covering: the row of every cell
`s` of `t` transforms to the stable section below `s`, capped at its value at `s`.  It is the
locality of a pointwise minimum of lawful sections (`Label.TransformsTo.inf`), collapsed above
`λ_ξ + N` for `N` above all grades (`Label.TransformsTo.collapse`). -/
theorem locality_stableSection (hR : R.IsConsistent) (hc : R.IsCovering)
    (ht : R.eval u = some t) (s : Fin t.card) :
    Label.TransformsTo
      (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦ t.toCellScheme.grade d)
      (t.rows.row s) (fun d ↦ min (R.stableSection u t d) (R.stableSection u t s)) := by
  by_cases hD : (univ.filter fun d ↦ t.label d = ⊤).Nonempty
  · obtain ⟨N, ℓ, hℓ, hkN, heq⟩ := exists_isLawful_collapse_inf' hR hc ht hD
    set D := univ.filter fun d ↦ t.label d = ⊤
    have key : Label.TransformsTo
        (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦ t.toCellScheme.grade d)
        (t.rows.row s) (fun e ↦ min (D.inf' hD fun j ↦ ℓ j e) (D.inf' hD fun j ↦ ℓ j s)) := by
      have h := inf'_induction hD
        (fun j (e : t.toCellScheme.below (t.toCellScheme.gradedIndex s)) ↦ min (ℓ j e) (ℓ j s))
        (p := Label.TransformsTo (fun d ↦ t.toCellScheme.grade d) (t.rows.row s))
        (fun _ h₁ _ h₂ ↦ h₁.inf h₂) fun j _ ↦ (hℓ j).locality s
      convert h using 1
      funext e
      rw [Finset.inf'_apply]
      exact le_antisymm (le_inf' _ _ fun j hj ↦ min_le_min (inf'_le _ hj) (inf'_le _ hj))
        (le_min (le_inf' _ _ fun j hj ↦ (inf'_le _ hj).trans (min_le_left _ _))
          (le_inf' _ _ fun j hj ↦ (inf'_le _ hj).trans (min_le_right _ _)))
    convert key.collapse (isSuccPrelimit_blockStage ξ)
      (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦ t.grade_le d) hkN using 1
    funext e
    simp only [Function.comp_apply, heq]
    exact ((Label.monotone_reduce _).map_min).symm
  · have h : ∀ d, R.stableSection u t d = t.label d := fun d ↦
      stableSection_of_ne_top fun hd ↦ hD ⟨d, mem_filter.mpr ⟨mem_univ _, hd⟩⟩
    simpa only [h] using t.isLawful.locality s

/-! ### Lawfulness: availability -/

/-- **Comparison through lifts**: for cells `a`, `b` of `t` labelled the formal top, if every lift
of `t` to `λ_ξ + ω` is at least as large at `b` as at `a`, then so is the stable section, since
every rooted cover forcing a threshold at `a` forces it at `b`. -/
private theorem stableSection_le_of_forall_lift (ht : R.eval u = some t) {a b : Fin t.card}
    (ha : t.label a = ⊤) (hb : t.label b = ⊤)
    (h : ∀ ℓ : Fin t.card → Label.{u}, t.rows.IsLawful ℓ →
      (∀ d, Label.AtStage (blockStage ξ + ω) (ℓ d)) →
        (∀ d, Label.reduce (blockStage ξ) (ℓ d) = t.label d) → ℓ a ≤ ℓ b) :
    R.stableSection u t a ≤ R.stableSection u t b := by
  rw [stableSection_of_eq_top ha, stableSection_of_eq_top hb]
  refine Label.ofOffset_mono (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
  obtain ⟨x, hx, hcov⟩ := (natCast_le_stableOffset_iff (covers_of_eval u ht) ha).mp hn
  refine (natCast_le_stableOffset_iff (covers_of_eval u ht) hb).mpr
    ⟨x, ⟨hx.1, fun Q P hQ hP i hi ↦ ?_⟩, hcov⟩
  obtain ⟨P', hP', hPt⟩ := exists_restrictFace_reduce_eq hx.1 hQ
  obtain rfl : P = P' := Option.some_injective _ (hP.symm.trans hP')
  obtain ⟨ℓ, hℓ, hcard, hℓP, hℓt⟩ := exists_isLawful_of_reduce_eq hPt
  have hat : ∀ d, Label.AtStage (blockStage ξ + ω) (ℓ d) := fun d ↦ by
    rw [hℓP d (Fin.cast hcard d) rfl, ← blockStage_add_one]
    exact P.atStage _
  rw [← hℓP b i hi.symm]
  exact (hx.2 Q P hQ hP (Fin.cast hcard a) rfl).trans
    ((hℓP a _ rfl).symm.trans_le (h ℓ hℓ hat hℓt))

/-- **Availability where the graded index carries at most one cell labelled the formal top**,
unconditional: if the cells of `t` labelled the formal top have distinct graded indices, the
stable section satisfies availability for every pair.  Every lift of `t` then carries, at the
unique cell labelled the formal top at the graded index of `t₀`, a label at least that of `s₀`, so
every threshold forced at `s₀` is forced there. -/
theorem availability_stableSection_of_injOn
    (hinj : Set.InjOn t.toCellScheme.gradedIndex {d | t.label d = ⊤}) (ht : R.eval u = some t)
    {s₀ t₀ : Fin t.card} (hst : t.toCellScheme.scope s₀ ⊆ t.toCellScheme.scope t₀)
    (hg : t.toCellScheme.grade s₀ = t.toCellScheme.grade t₀) :
    ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧
      R.stableSection u t s₀ ≤ R.stableSection u t w := by
  obtain ⟨w, hw, hle⟩ := t.isLawful.availability s₀ t₀ hst hg
  refine ⟨w, hw, ?_⟩
  by_cases hs₀ : t.label s₀ = ⊤
  swap
  · exact stableSection_le_of_ne_top hs₀ hle
  have hw' : t.label w = ⊤ := top_le_iff.mp (hs₀ ▸ hle)
  refine stableSection_le_of_forall_lift ht hs₀ hw' fun ℓ hℓ _ hℓt ↦ ?_
  obtain ⟨w', hw'', hle'⟩ := hℓ.availability s₀ t₀ hst hg
  have htop : t.label w' = ⊤ := by
    rw [← hℓt w']
    exact Label.reduce_of_le ((Label.reduce_eq_top_iff.mp ((hℓt s₀).trans hs₀)).trans hle')
  rwa [hinj htop hw' (hw''.trans hw.symm)] at hle'

/-! ### Stable lawfulness -/

/-- **Stable lawfulness without twins**: an exactly consistent covering realization in whose types
no two cells labelled the formal top share a graded index is stably lawful.  Legal types are not
assumed (compare `isStablyLawful_of_hasLegalTypes`). -/
theorem isStablyLawful_of_injOn_gradedIndex (hR : R.IsConsistent) (hc : R.IsCovering)
    (hinj : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
      Set.InjOn t.toCellScheme.gradedIndex {d | t.label d = ⊤}) : R.IsStablyLawful :=
  fun _ u t ht ↦
    { orderly := orderly_stableSection ht
      locality := locality_stableSection hR hc ht
      availability := fun _ _ hst hg ↦ availability_stableSection_of_injOn (hinj u t ht) ht hst hg }

/-! ### Cover-hollow realizations -/

/-- In a cover-hollow realization the stable section is the label section. -/
theorem stableSection_eq_label_of_isCoverHollow (hh : R.IsCoverHollow) (ht : R.eval u = some t) :
    R.stableSection u t = t.label := funext fun d ↦ by
  by_cases hd : t.label d = ⊤
  · rw [stableSection_of_eq_top hd, hd]
    exact isCoverHollow_iff_forall_stableLabel_eq_top.mp hh ⟨k, u, t, ht⟩ d hd
  · exact stableSection_of_ne_top hd

/-- **A cover-hollow realization is stably lawful**, with no hypothesis. -/
theorem isStablyLawful_of_isCoverHollow (hh : R.IsCoverHollow) : R.IsStablyLawful :=
  fun _ _ t ht ↦ stableSection_eq_label_of_isCoverHollow hh ht ▸ t.isLawful

/-- In a cover-hollow realization the candidate is `R` read at `λ_{ξ+1}`. -/
theorem stableCandidate_eval_of_isCoverHollow (hh : R.IsCoverHollow) (hlaw : R.IsStablyLawful)
    (u : Fin k ↪ M) :
    (R.stableCandidate hlaw).eval u =
      (R.eval u).map (castLE · (blockStage_lt_blockStage_add_one ξ).le) := by
  cases h : R.eval u with
  | none => exact stableCandidate_eval_eq_none_iff.mpr h
  | some t =>
    rw [stableCandidate_eval_of_eval h, Option.map_some]
    exact congrArg some (StageType.ext rfl fun i j hij ↦ by
      rw [Fin.ext hij]
      exact congrFun (stableSection_eq_label_of_isCoverHollow hh h) j)

/-- **The candidate of a cover-hollow realization is not a model.**  Its labels
are those of `R`, below `λ_ξ` or the formal top, so uniformity at `γ = λ_ξ` fails. -/
theorem not_isModel_stableCandidate_of_isCoverHollow (hh : R.IsCoverHollow)
    (hlaw : R.IsStablyLawful) : ¬ (R.stableCandidate hlaw).IsModel := fun hM ↦ by
  obtain ⟨x⟩ := hM.nonempty_occurrence
  obtain ⟨w, -, q, ⟨d, h₁, h₂⟩, hq⟩ := hM.uniformity x _ (isSuccPrelimit_blockStage ξ)
    (blockStage_lt_blockStage_add_one ξ)
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hq
  have hd := congrFun (stableSection_eq_label_of_isCoverHollow hh ht) d
  replace h₁ : ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ t.label d := hd ▸ h₁
  replace h₂ : t.label d < ((blockStage ξ + ω : Ordinal.{u}) : Label.{u}) := hd ▸ h₂
  rcases t.atStage d with h | h
  · exact h₁.not_gt h
  · exact (h ▸ h₂).not_ge le_top

/-! ### Bounded stable labels -/

/-- **Bounded stable labels refute modelhood.**  If every stable label at a cell labelled the
formal top is at most `λ_ξ + K`, every label of the candidate is at most `λ_ξ + K`, and high-arity
dominance at `γ = λ_ξ + K` fails, so the candidate is not a model. -/
theorem not_isModel_stableCandidate_of_stableLabel_le {K : ℕ}
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{u}) : Label.{u}))
    (hlaw : R.IsStablyLawful) : ¬ (R.stableCandidate hlaw).IsModel := fun hM ↦ by
  obtain ⟨x⟩ := hM.nonempty_occurrence
  obtain ⟨w, -, q, ⟨d, -, h⟩, hq⟩ := hM.dominance x (blockStage ξ + K) (by
    rw [blockStage_add_one]
    exact add_lt_add_right (natCast_lt_omega0 K) _)
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hq
  refine h.not_ge ?_
  -- the label of the stable type at `d` is the stable section there
  change R.stableSection w t d ≤ _
  by_cases hd : t.label d = ⊤
  · rw [stableSection_of_eq_top hd]
    exact hK w t ht d hd
  · rw [stableSection_of_ne_top hd]
    exact ((t.atStage d).resolve_right hd).le.trans (Label.coe_le_coe_add _ K)

/-! ### A model expansion -/

/-- **Stable lawfulness from a model expansion**, conditional on forcing donors at `ξ` (compiled in
this repository (theorem named) at every block index, `forcingDonors_blockStage`) and on
finite-extension receiving of `R'` (from (R1), still to be proved): if `R` is the reduction of an
exactly consistent realization `R'` at `λ_{ξ+1}` with legal types, the stable section at every typed
tuple is the label section of its type in `R'` (normalization), so `R` is stably lawful. -/
theorem isStablyLawful_of_reduce_eq (hF : ForcingDonors.{u} ξ)
    {R' : Realization.{u, v} (blockStage (ξ + 1)) M} (hR' : R'.IsConsistent)
    (hl' : R'.HasLegalTypes) (hrec' : R'.HasFiniteExtensionReceiving)
    (h : R'.reduce (isSuccPrelimit_blockStage ξ) = R) : R.IsStablyLawful := fun _ u t ht ↦ by
  subst h
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp ht
  have heq : (R'.reduce (isSuccPrelimit_blockStage ξ)).stableSection u
      (T.reduce (isSuccPrelimit_blockStage ξ)) = T.label := funext fun d ↦ by
    by_cases hd : (T.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤
    · rw [stableSection_of_eq_top hd]
      exact (label_eq_stableLabel hR' hl' hrec' hF (covers_of_eval u hT) d hd).symm
    · rw [stableSection_of_ne_top hd]
      have hlt : Label.reduce (blockStage ξ) (T.label d) < blockStage ξ :=
        ((T.reduce _).atStage d).resolve_right hd
      exact Label.reduce_of_lt (Label.reduce_lt_iff.mp hlt)
  rw [heq]
  exact T.isLawful

end Realization

/-! ### Availability at twins from legal types -/

namespace Realization

section Availability

variable {ξ : Ordinal.{u}} {M : Type v} {k : ℕ} {R : Realization.{u, v} (blockStage ξ) M}

variable (R) in
/-- **Forcing over a realized rooted cover**: some rooted cover `(m, q, f)` of `u` realized in `R`
(the tuple `u` extends along `f` to a cover of `q`) forces the threshold `n` at the cell `d` of `t`,
read at `λ_{ξ+1}`. -/
def ForcesOverCover (u : Fin k ↪ M) (t : StageType.{u} (blockStage ξ) k) (d : Fin t.card)
    (n : ℕ) : Prop :=
  ∃ x : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin k ↪ Fin m),
    ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.2.1 x.2.2 t d n ∧
      R.ExtendsToCover u x

/-- **Availability of the stable section at a cell labelled the formal top**: at a typed tuple `u`
of type `t` and a cell `s₀` labelled the formal top, the availability law of the stable section
for the pair `(s₀, t₀)` holds exactly when every threshold forced at `s₀` over a realized rooted
cover is forced, over a realized rooted cover, at some cell labelled the formal top at the graded
index of `t₀`.  No hypothesis on `R`; the cell may depend on the threshold, and the law takes the
one with the largest stable offset. -/
theorem availability_stableSection_iff {u : Fin k ↪ M} {t : StageType.{u} (blockStage ξ) k}
    (ht : R.eval u = some t) {s₀ t₀ : Fin t.card} (hs₀ : t.label s₀ = ⊤) :
    (∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧
        R.stableSection u t s₀ ≤ R.stableSection u t w) ↔
      ∀ n : ℕ, R.ForcesOverCover u t s₀ n →
        ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧ t.label w = ⊤ ∧
          R.ForcesOverCover u t w n := by
  have hc : R.Covers t u := covers_of_eval u ht
  constructor
  · rintro ⟨w, hw, hle⟩ n hn
    have h₁ : ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) ≤ R.stableSection u t s₀ := by
      rw [stableSection_of_eq_top hs₀]
      exact (coe_add_le_stableLabel_iff hc hs₀).mpr hn
    have hwt : t.label w = ⊤ := by
      by_contra hwt
      rw [stableSection_of_ne_top hwt] at hle
      exact (h₁.trans hle).not_gt (((t.atStage w).resolve_right hwt).trans_le
        (Label.coe_le_coe_add _ _))
    refine ⟨w, hw, hwt, ?_⟩
    have h₂ := h₁.trans hle
    rw [stableSection_of_eq_top hwt] at h₂
    exact (coe_add_le_stableLabel_iff hc hwt).mp h₂
  · intro h
    classical
    set T := univ.filter fun w : Fin t.card ↦
      t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧ t.label w = ⊤
    set o : Fin t.card → ℕ∞ := fun d ↦
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d
    have hT : T.Nonempty := by
      obtain ⟨w, hw, hwt, -⟩ := h 0 ⟨⟨k, t, Function.Embedding.refl _⟩,
        forcesThreshold_zero (restrictFace_refl t) hs₀, u, rfl, hc⟩
      exact ⟨w, mem_filter.mpr ⟨mem_univ _, hw, hwt⟩⟩
    obtain ⟨w₀, hw₀, hmax⟩ := T.exists_max_image o hT
    obtain ⟨-, hw₀i, hw₀t⟩ := mem_filter.mp hw₀
    refine ⟨w₀, hw₀i, ?_⟩
    rw [stableSection_of_eq_top hs₀, stableSection_of_eq_top hw₀t]
    refine Label.ofOffset_mono (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
    obtain ⟨w, hw, hwt, hf⟩ := h n ((natCast_le_stableOffset_iff hc hs₀).mp hn)
    exact ((natCast_le_stableOffset_iff hc hwt).mpr hf).trans
      (hmax w (mem_filter.mpr ⟨mem_univ _, hw, hwt⟩))

/-- **Availability of the stable section from legal types**, at every typed tuple and every pair,
with no hypothesis on `R` beyond the legality of its types.  At a first cell labelled the formal
top, the rooted cover that forces a threshold there forces it at a cell labelled the formal top at
the graded index of the second cell (`StageType.exists_forcesThreshold_twin_face`), and
`availability_stableSection_iff` applies. -/
theorem availability_stableSection_of_hasLegalTypes (hl : R.HasLegalTypes)
    {u : Fin k ↪ M} {t : StageType.{u} (blockStage ξ) k} (ht : R.eval u = some t)
    {s₀ t₀ : Fin t.card} (hst : t.toCellScheme.scope s₀ ⊆ t.toCellScheme.scope t₀)
    (hg : t.toCellScheme.grade s₀ = t.toCellScheme.grade t₀) :
    ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧
      R.stableSection u t s₀ ≤ R.stableSection u t w := by
  by_cases hs : t.label s₀ = ⊤
  · refine (availability_stableSection_iff ht hs).mpr fun n ⟨x, hx, hcov⟩ ↦ ?_
    obtain ⟨s, hs', hcs⟩ := hcov
    obtain ⟨w, hw, hwt, hwf⟩ := exists_forcesThreshold_twin_face
      (blockStage_add_one ξ).ge (hl _ _ hcs.eval_eq) hx.1 hst hg hs hx
    exact ⟨w, hw, hwt, x, hwf, s, hs', hcs⟩
  · obtain ⟨w, hw, hle⟩ := t.isLawful.availability s₀ t₀ hst hg
    exact ⟨w, hw, stableSection_le_of_ne_top hs hle⟩

/-- **Stable lawfulness from legal types**: every exactly consistent covering realization with
legal types at a block stage is stably lawful.  The order law needs no hypothesis, locality comes
from exact consistency and covering, and availability from legal types. -/
theorem isStablyLawful_of_hasLegalTypes (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes) : R.IsStablyLawful := fun _ _ _ ht ↦
  { orderly := orderly_stableSection ht
    locality := locality_stableSection hR hc ht
    availability := fun _ _ hst hg ↦ availability_stableSection_of_hasLegalTypes hl ht hst hg }

/-- **Every model at a block stage is stably lawful.** -/
theorem IsModel.isStablyLawful (hR : R.IsModel) : R.IsStablyLawful :=
  isStablyLawful_of_hasLegalTypes hR.isConsistent hR.isCovering hR.hasLegalTypes

end Availability

end Realization

end VaughtConjecture

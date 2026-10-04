/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Label.Transform
import VaughtConjecture.Realization.BlockStages
import VaughtConjecture.Realization.Families
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

**Two of the three laws.**  Fix a typed tuple `u` of type `t`.

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

The third law, availability, is not treated here: the pointwise minimum of lawful lifts need not
satisfy it when one graded index carries two cells labelled the formal top (the stage-type example
of `VaughtConjecture.Stage.ThresholdExamples`).

**Relation to the roadmap.**  The roadmap builds the structural candidate "from consistency and
covering" (Layer 4, output 1).  Here the order law, locality, exact partial evaluation, the
reduction, legality, covering and exact consistency need no more.  The splice of two witnesses
(roadmap, Layer 3, the transformation lemma still to be proved there) is not used: locality comes
from pointwise minima and collapse.

**What is not claimed.**  Stable lawfulness (availability in particular) and the modelhood of the
candidate (output 3) are not proved here.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Ordinal StageType

/-! ### Auxiliary facts -/

/-- `β ≤ β + n` as labels. -/
private theorem coe_le_coe_add (β : Ordinal.{u}) (n : ℕ) :
    (β : Label.{u}) ≤ ((β + n : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

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
      Label.reduce_of_lt (((t.atStage e).resolve_right he).trans_le (coe_le_coe_add β N))]

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

end Realization

end VaughtConjecture

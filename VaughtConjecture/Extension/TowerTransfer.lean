/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.TopFreePinnedExtension

/-!
# Towers and their transfer to a larger base

**Towers.**  A stage type `T` on `n` points is a *tower over* `p` along `e : Fin m ↪ Fin n`
(`StageType.IsTowerOver`) when it is reached from `p` by adding one last point at a time, each
earlier type being the face of the next along the initial segment.  The arity is an index of the
inductive predicate, so no arithmetic on `Fin` is needed to state it.  A tower restricts to its
base along `e` (`StageType.IsTowerOver.restrictFace_eq`), its base map is the initial segment
(`StageType.IsTowerOver.val_apply`), every initial segment of length between `m` and `n` is a
closed face, itself a tower over `p` (`StageType.IsTowerOver.exists_restrictFace_castLEEmb`), and
towers compose (`StageType.IsTowerOver.trans`).

**The tower transfer.**  At a limit stage, let `T` be a legal top-free tower over `p` along `e`,
and let `P'` be legal and top-free with `p` as its face along `g`.  Then some legal top-free `Q` is
a tower over `P'` along `e'`, with `T` as its face along a map `G` such that
(`StageType.exists_isTopFree_tower_transfer`, target `StageType.TowerTransferTarget`):

* `e.trans G = g.trans e'` (the base of `T` is carried along `g`);
* **exact overlap**: `e' i = G j` exactly when `i = g k` and `j = e k` for some `k`;
* every point of `Q` is a point of `P'` or of `T`;
* the points added to `T` keep their order: `G j` is `m' + (j - m)` for `j ≥ m`, and `Q` has
  `m' + (n - m)` points.

The proof is an induction on the tower: each added point of `T` is re-attached over the transfer of
the previous stage by the top-free pinned extension (`StageType.exists_isTopFree_pinned_extension`)
with the stage of `T` itself as the donor.  The new point is the last point, so it is outside the
image of `P'`, which keeps the overlap exact.

**Why the position formula.**  Every closed subface of `T` stays closed along `G`, by composition
of restrictions (`StageType.restrictFace_trans`).  What is not automatic is that its union with the
enlarged base `P'` is closed.  For the stages of the tower it is: by the point count and the
position formula, for `m ≤ r ≤ n` the enlarged base together with the first `r` positions of `T`
is the initial segment of `Q` of length `m' + (r - m)`, a stage of the tower `Q`, hence closed
(`StageType.IsTowerOver.exists_restrictFace_castLEEmb`).

**One-point cofaces.**  At a limit stage every legal top-free stage type has a top-free one-point
coface (`StageType.exists_isTopFree_mem_cofaces`): the pinned extension along the empty face, with
the one-point apex type capped below the stage as the donor.

## Placement

This file belongs to Layer 3 of `roadmap/README.md` (beside the top-free pinned extension); it is
the finite step of the descending block of the `ℵ₁` companion construction
(`VaughtConjecture.Realization.SuffixCharts`, `VaughtConjecture.AlephOne.DescendingBlock`).
-/

universe u

namespace VaughtConjecture.StageType

variable {α : Ordinal.{u}} {m : ℕ}

/-- `T` on `n` points is a **tower over** `p` along `e`: `T` is reached from `p` by adding one last
point at a time, the face of each stage along the initial segment being the previous stage. -/
inductive IsTowerOver (p : StageType.{u} α m) :
    ∀ {n : ℕ}, (Fin m ↪ Fin n) → StageType.{u} α n → Prop
  /-- A stage type is a tower over itself along the identity. -/
  | refl : IsTowerOver p (Function.Embedding.refl _) p
  /-- A one-point coface of a tower, along the initial segment, is a tower. -/
  | snoc {n : ℕ} {e : Fin m ↪ Fin n} {T : StageType.{u} α n} {D : StageType.{u} α (n + 1)} :
      IsTowerOver p e T → restrictFace Fin.castSuccEmb D = some T →
        IsTowerOver p (e.trans Fin.castSuccEmb) D

namespace IsTowerOver

variable {p : StageType.{u} α m}

/-- A tower restricts to its base along its base map. -/
theorem restrictFace_eq {n : ℕ} {e : Fin m ↪ Fin n} {T : StageType.{u} α n}
    (h : IsTowerOver p e T) : restrictFace e T = some p := by
  induction h with
  | refl => exact restrictFace_refl _
  | snoc _ hD ih => rw [← restrictFace_trans _ _ _ hD, ih]

/-- The base map of a tower is the initial segment. -/
theorem val_apply {n : ℕ} {e : Fin m ↪ Fin n} {T : StageType.{u} α n}
    (h : IsTowerOver p e T) (i : Fin m) : (e i : ℕ) = i := by
  induction h with
  | refl => rfl
  | snoc _ _ ih => simp [ih]

/-- A tower has at least as many points as its base. -/
theorem le {n : ℕ} {e : Fin m ↪ Fin n} {T : StageType.{u} α n} (h : IsTowerOver p e T) :
    m ≤ n := by
  induction h with
  | refl => exact le_rfl
  | snoc _ _ ih => exact ih.trans (Nat.le_succ _)

/-- A one-point coface is a one-step tower. -/
theorem single {D : StageType.{u} α (m + 1)} (hD : restrictFace Fin.castSuccEmb D = some p) :
    IsTowerOver p Fin.castSuccEmb D := by
  simpa using IsTowerOver.refl.snoc hD

/-- **Towers compose**: a tower over `E` along `e'`, with `E` a tower over `p` along `e`, is a
tower over `p` along `e.trans e'`. -/
theorem trans {k : ℕ} {e : Fin m ↪ Fin k} {E : StageType.{u} α k} (hE : IsTowerOver p e E)
    {n : ℕ} {e' : Fin k ↪ Fin n} {T : StageType.{u} α n} (hT : IsTowerOver E e' T) :
    IsTowerOver p (e.trans e') T := by
  induction hT with
  | refl => simpa using hE
  | snoc _ hD ih => simpa [Function.Embedding.trans_assoc] using ih.snoc hD

/-- Two embeddings into `Fin n` with the same values are equal. -/
private theorem embedding_eq_castLEEmb {r n : ℕ} {f : Fin r ↪ Fin n} (hrn : r ≤ n)
    (hf : ∀ i, (f i : ℕ) = i) : f = Fin.castLEEmb hrn :=
  Function.Embedding.ext fun i ↦ Fin.ext (by simp [hf])

/-- **Every stage of a tower is a closed face**: for `m ≤ r ≤ n`, the initial segment of length
`r` of a tower over `p` is a closed face, and its restriction is a tower over `p` along the initial
segment. -/
theorem exists_restrictFace_castLEEmb {n : ℕ} {e : Fin m ↪ Fin n} {T : StageType.{u} α n}
    (h : IsTowerOver p e T) {r : ℕ} (hmr : m ≤ r) (hrn : r ≤ n) :
    ∃ q, restrictFace (Fin.castLEEmb hrn) T = some q ∧ IsTowerOver p (Fin.castLEEmb hmr) q := by
  induction h generalizing r with
  | refl =>
    obtain rfl := le_antisymm hrn hmr
    refine ⟨p, ?_, ?_⟩
    · rw [← embedding_eq_castLEEmb hrn (f := Function.Embedding.refl _) fun _ ↦ rfl]
      exact restrictFace_refl _
    · rw [← embedding_eq_castLEEmb hmr (f := Function.Embedding.refl _) fun _ ↦ rfl]
      exact IsTowerOver.refl
  | @snoc n e T D hT hD ih =>
    rcases Nat.lt_or_ge r (n + 1) with hlt | hge
    · obtain ⟨q, hq, hqt⟩ := ih hmr (Nat.le_of_lt_succ hlt)
      refine ⟨q, ?_, hqt⟩
      rw [← hq, restrictFace_trans _ _ _ hD]
      exact congrArg (restrictFace · D) (Function.Embedding.ext fun _ ↦ Fin.ext rfl)
    · obtain rfl := le_antisymm hrn hge
      refine ⟨D, by rw [← embedding_eq_castLEEmb hrn (f := Function.Embedding.refl _)
        fun _ ↦ rfl]; exact restrictFace_refl _, ?_⟩
      rw [← embedding_eq_castLEEmb hmr (f := e.trans Fin.castSuccEmb)
        fun i ↦ by simp [hT.val_apply i]]
      exact hT.snoc hD

end IsTowerOver

/-- **Target: transfer of a tower to a larger base.**  At a limit stage `α`, let `T` on `n` points
be a legal top-free tower over `p` along `e`, and let `P'` on `m'` points be legal and top-free
with `p` as its face along `g`.  Then some legal top-free `Q` on `n'` points is a tower over `P'`
along `e'` and has `T` as its face along `G`, where `e.trans G = g.trans e'`; the two faces overlap
exactly in the base (`e' i = G j` exactly when `i = g k` and `j = e k` for some `k`); every point
of `Q` is a point of `P'` or of `T`; `n' + m = m' + n`; and the points added to `T` keep their
order (`G j + m = m' + j` for `j ≥ m`).  Proved (`StageType.towerTransferTarget`). -/
def TowerTransferTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m m' n : ℕ⦄, Order.IsSuccLimit α →
    ∀ ⦃p : StageType.{u} α m⦄ ⦃e : Fin m ↪ Fin n⦄ ⦃T : StageType.{u} α n⦄,
      T.IsLegal → T.IsTopFree → IsTowerOver p e T →
    ∀ ⦃P' : StageType.{u} α m'⦄ ⦃g : Fin m ↪ Fin m'⦄, P'.IsLegal → P'.IsTopFree →
      restrictFace g P' = some p →
        ∃ (n' : ℕ) (Q : StageType.{u} α n') (e' : Fin m' ↪ Fin n') (G : Fin n ↪ Fin n'),
          Q.IsLegal ∧ Q.IsTopFree ∧ IsTowerOver P' e' Q ∧ restrictFace G Q = some T ∧
          e.trans G = g.trans e' ∧ (∀ i j, e' i = G j ↔ ∃ k, i = g k ∧ j = e k) ∧
          (∀ x, x ∈ Set.range e' ∨ x ∈ Set.range G) ∧ n' + m = m' + n ∧
          ∀ j : Fin n, m ≤ (j : ℕ) → (G j : ℕ) + m = m' + j

/-- **Transfer of a tower to a larger base.**  Induction on the tower.  At the base, `Q = P'` and
`G = g`.  At a step `D` over `T₀`, the transfer `Q₀` of `T₀` (with face map `G₀`) is extended by
one point by the top-free pinned extension (`StageType.exists_isTopFree_pinned_extension`) of
`Q₀` along `G₀` with donor `D`; the new point is last, so it is the image of the last point of `D`
under `extendByLast G₀` and lies outside the image of `P'`. -/
theorem exists_isTopFree_tower_transfer {α : Ordinal.{u}} {m m' n : ℕ}
    (hα : Order.IsSuccLimit α) {p : StageType.{u} α m} {e : Fin m ↪ Fin n}
    {T : StageType.{u} α n} (hT : T.IsLegal) (hTt : T.IsTopFree) (h : IsTowerOver p e T)
    {P' : StageType.{u} α m'} {g : Fin m ↪ Fin m'} (hP' : P'.IsLegal) (hP't : P'.IsTopFree)
    (hg : restrictFace g P' = some p) :
    ∃ (n' : ℕ) (Q : StageType.{u} α n') (e' : Fin m' ↪ Fin n') (G : Fin n ↪ Fin n'),
      Q.IsLegal ∧ Q.IsTopFree ∧ IsTowerOver P' e' Q ∧ restrictFace G Q = some T ∧
      e.trans G = g.trans e' ∧ (∀ i j, e' i = G j ↔ ∃ k, i = g k ∧ j = e k) ∧
      (∀ x, x ∈ Set.range e' ∨ x ∈ Set.range G) ∧ n' + m = m' + n ∧
      ∀ j : Fin n, m ≤ (j : ℕ) → (G j : ℕ) + m = m' + j := by
  induction h with
  | refl =>
    refine ⟨m', P', Function.Embedding.refl _, g, hP', hP't, IsTowerOver.refl, hg, rfl,
      fun i j ↦ ⟨fun hij ↦ ⟨j, hij, rfl⟩, fun ⟨k, hik, hjk⟩ ↦ hjk ▸ hik⟩,
      fun x ↦ Or.inl ⟨x, rfl⟩, rfl, fun j hj ↦ absurd j.isLt (by omega)⟩
  | @snoc n e T₀ D hT₀ hD ih =>
    obtain ⟨n₀, Q₀, e₀, G₀, hQ₀, hQ₀t, htow, hG₀, hcomm, hover, hcov, hcard, hord⟩ :=
      ih (hT.restrictFace _ hD) (hTt.restrictFace hD)
    obtain ⟨Q, hQ, hQt, hQQ₀, hQD⟩ :=
      exists_isTopFree_pinned_extension hα hQ₀ hQ₀t hG₀ hT hTt hD
    refine ⟨n₀ + 1, Q, e₀.trans Fin.castSuccEmb, extendByLast G₀, hQ, hQt, htow.snoc hQQ₀, hQD,
      ?_, fun i j ↦ ?_, fun x ↦ ?_, by omega, fun j hj ↦ ?_⟩
    · refine Function.Embedding.ext fun i ↦ ?_
      simpa using congrArg Fin.castSucc (DFunLike.congr_fun hcomm i)
    · induction j using Fin.lastCases with
      | last =>
        simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, extendByLast_last]
        exact ⟨fun hx ↦ absurd hx (Fin.castSucc_lt_last _).ne,
          fun ⟨k, _, hk⟩ ↦ absurd hk.symm (Fin.castSucc_lt_last _).ne⟩
      | cast j =>
        simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, extendByLast_castSucc,
          Fin.castSucc_inj]
        exact hover i j
    · induction x using Fin.lastCases with
      | last => exact Or.inr ⟨Fin.last n, extendByLast_last _⟩
      | cast x =>
        rcases hcov x with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨j.castSucc, extendByLast_castSucc _ _⟩
    · induction j using Fin.lastCases with
      | last => simp only [extendByLast_last, Fin.val_last]; omega
      | cast j =>
        simp only [extendByLast_castSucc, Fin.val_castSucc] at hj ⊢
        exact hord j hj

/-- **A top-free one-point coface at a limit stage.**  Every legal top-free stage type at a limit
stage has a top-free one-point coface: the top-free pinned extension along the empty face
(`StageType.exists_isTopFree_pinned_extension`), with donor the one-point apex type
(`StageType.onePointApex`) capped at an ordinal below the stage, self-visible at `1`
(`StageType.exists_cap`). -/
theorem exists_isTopFree_mem_cofaces {α : Ordinal.{u}} {n : ℕ} (hα : Order.IsSuccLimit α)
    {P : StageType.{u} α n} (hP : P.IsLegal) (hPt : P.IsTopFree) :
    ∃ E ∈ P.cofaces, E.IsTopFree := by
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  have hp₀t := hPt.restrictFace hp₀
  obtain ⟨c, hcα, hc, -, -⟩ := exists_cap hα.isSuccPrelimit
    (by simpa [Ordinal.bot_eq_zero] using hα.bot_lt) hp₀t hp₀t 1
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (((onePointApex (α := α)).cap c hc hcα).isSome_restrictFace_of_zero
      (Fin.castSuccEmb : Fin 0 ↪ Fin 1))
  obtain rfl : q = p₀ := eq_of_zero q p₀
  obtain ⟨Q, hQ, hQt, hQP, -⟩ := exists_isTopFree_pinned_extension hα hP hPt hp₀
    (isLegal_cap.mpr isLegal_onePointApex) isTopFree_cap hq
  exact ⟨Q, ⟨hQ, hQP⟩, hQt⟩

/-- **Transfer of a tower to a larger base**, the target form
(`StageType.exists_isTopFree_tower_transfer`). -/
theorem towerTransferTarget : TowerTransferTarget.{u} :=
  fun _ _ _ _ hα _ _ _ hT hTt h _ _ hP' hP't hg ↦
    exists_isTopFree_tower_transfer hα hT hTt h hP' hP't hg

end VaughtConjecture.StageType

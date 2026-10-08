/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapCoatomRelabel
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem
import VaughtConjecture.MainTheorem.ReceivingDetermination

/-!
# Cutoff determination at the first coatom

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4, and 3.4: the exact pinned extension); semantic
contract, items 4 and 5.

Cutoff determination (`Realization.CutoffDetermination`) and hollow cutoff determination
(`Realization.HollowCutoffDetermination`) ask, over a legal context `t'` along a root `h`, for one
coface `D'` of `t'` and one permitted cutoff `δ` such that every member of the receiving family of
`D'` at `δ` with face `t'` has the donor `d` as its face along the root.  This file reduces both to
their **coatom forms**, in which the root lies in the first coatom `Fin.castSuccEmb` and the donor
is the face of a coface `tb` of the coatom face.  Each item below is compiled in this repository
(theorem named), unless marked otherwise.

**Relabelling** (`StageType.extendPerm`, in `VaughtConjecture.Extension.Basic`;
`StageType.reindex_extendPerm_symm_mem_cofaces`, in `VaughtConjecture.Realization.Families`;
`StageType.IsDeterminedWithin.reindex_extendPerm`, in
`VaughtConjecture.Continuation.ExactReceiving`).  For a permutation `σ` of the points of `t'`,
let `τ` be its extension fixing the new point.  A coface `D''` of `t'.reindex σ` gives the coface
`D''.reindex τ⁻¹` of `t'`, and determination of `d` over `t'.reindex σ` along `h''` within the
receiving family of `D''` at `δ` gives determination of `d` over `t'` along `h''.trans σ` within
the receiving family of `D''.reindex τ⁻¹` at `δ` (receiving families reindex,
`StageType.reindex_mem_receivingFamily`).

**The coatom forms** (`Realization.CoatomCutoffDetermination`,
`Realization.HollowCoatomCutoffDetermination`, statements about stage types, open for every
predicate of interest).  The context is `t'` on `k + 1` points with the root `g.trans
Fin.castSuccEmb`, the coatom face is `p` (the face of `t'` along `Fin.castSuccEmb`), and `tb` is
any legal coface of `p` whose face along `g` followed by the new point is `d`.  One coface `D'` of
`t'` with face `tb` along `extendByLast Fin.castSuccEmb` (a completion of the coatom pair
`(t', tb)` over `p`) and one permitted cutoff `δ` are chosen for the input, and `d` must be
determined over `t'` within the receiving family of `D'` at `δ`.  The donor side `tb` is not
controlled by anything: the determination is asked only along the root.  The coatom forms are
stronger hypotheses than the original forms: they imply them (below), and no converse is claimed.
In the (R2) form `tb` ranges over every legal coface of `p`, also of top grade above `K`.  The
clause that `D'` has face `tb` is not used by the reductions below; without it the coatom form
would be an exact reformulation of the original form at the inputs whose root lies in the first
coatom, since `tb` always exists.

**The reductions** (`Realization.CoatomCutoffDetermination.cutoffDetermination`,
`Realization.HollowCoatomCutoffDetermination.hollowCutoffDetermination`).  For a predicate `P` on
contexts such that no root of an acquired context is onto and `P` is invariant under relabelling
the points of the context (with the root relabelled along), the coatom form gives the original
form.  The root lies in a closed coatom (`StageType.exists_coatom_trans_eq`); a relabelling makes
the coatom the first one (`StageType.exists_perm_castSuccEmb_trans`); the exact pinned extension
(`StageType.exists_pinned_extension`, from the coatom extension property at every stage that is
zero or a limit, `StageType.hasCoatomExtensions`) gives `tb`; the coatom form gives the coface and
the cutoff; and relabelling back gives determination over `t'`.  The coatom extension property is
compiled, so it is not a hypothesis.  The castSucc cases
(`Realization.CoatomCutoffDetermination.exists_coface_castSucc`,
`Realization.HollowCoatomCutoffDetermination.exists_coface_castSucc`) need no relabelling and no
invariance: they apply when the root of the acquired context already lies in the first coatom (the
lost point last, in the acquisition of (R2)).

**Not claimed.**  That the coatom forms hold for the source-gap or the marked-cap contexts: that is
the finite construction of the carrier, open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Realization

open StageType

/-! ### The coatom forms -/

/-- **Coatom cutoff determination** for `P`, a statement about stage types: at a limit stage, over
every legal `t'` on `k + 1` points with `P K t' (g.trans Fin.castSuccEmb)` and face `p` along
`Fin.castSuccEmb`, for every legal coface `tb` of `p` whose face along `g` followed by the new
point is a donor `d` of top grade at most `K`, some coface `D'` of `t'` with face `tb` along
`extendByLast Fin.castSuccEmb` and some permitted cutoff `δ` determine `d` over `t'` along
`g.trans Fin.castSuccEmb` within the receiving family of `D'` at `δ`.  The coface and the cutoff
are chosen for the input, before any member of the family.  Not proved for any `P` here. -/
structure CoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every donor through a coface of the coatom face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P K t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
        restrictFace (extendByLast g) tb = some d → d.topGrade ≤ K →
          ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
            ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
              IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Hollow coatom cutoff determination** for `P`: the statement of `CoatomCutoffDetermination`
without the bound on the top grade of the donor.  Not proved for any `P` here. -/
structure HollowCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every donor through a coface of the coatom face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
        restrictFace (extendByLast g) tb = some d →
          ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
            ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
              IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Coatom cutoff determination is antitone in the predicate**: coatom cutoff determination for
`P` gives it for every predicate `P'` that implies `P`. -/
theorem CoatomCutoffDetermination.mono
    {P P' : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : CoatomCutoffDetermination.{u} P)
    (hP : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P' K t' h → P K t' h) :
    CoatomCutoffDetermination.{u} P' where
  exists_coface _ _ _ _ t' g p hα ht' hP' := hdet.exists_coface t' g p hα ht' (hP _ _ hP')

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A coface of the coatom face through the donor**: at a limit stage, for a legal `t'` with
face `p` along `Fin.castSuccEmb` and face `t` along `g.trans Fin.castSuccEmb`, every coface `d` of
`t` is the face along `extendByLast g` of a legal coface of `p` (the exact pinned extension, from
the compiled coatom extension property). -/
theorem exists_mem_cofaces_restrictFace_eq (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) : ∃ tb ∈ p.cofaces, restrictFace (extendByLast g) tb = some d := by
  have hpt : restrictFace g p = some t := (restrictFace_trans t' _ g hp).trans ht
  obtain ⟨tb, htb, htbp, htbd⟩ := exists_pinned_extension (hasCoatomExtensions hα.isSuccPrelimit)
    (ht'.restrictFace _ hp) hpt hd.1 hd.2
  exact ⟨tb, ⟨htb, htbp⟩, htbd⟩

/-- **The coatom form at a root in the first coatom**: coatom cutoff determination gives the
conclusion of cutoff determination at every input whose root is `g.trans Fin.castSuccEmb` and
whose first coatom is a closed face.  No relabelling and no invariance of `P` is used. -/
theorem CoatomCutoffDetermination.exists_coface_castSucc
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : CoatomCutoffDetermination.{u} P) {K : ℕ} (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) {g : Fin n ↪ Fin k}
    (hP : P K t' (g.trans Fin.castSuccEmb)) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d := by
  obtain ⟨tb, htb, htbd⟩ := exists_mem_cofaces_restrictFace_eq hα ht' hp ht hd
  obtain ⟨D', hD', -, hrest⟩ := hdet.exists_coface t' g p hα ht' hP hp tb htb d htbd hdK
  exact ⟨D', hD', hrest⟩

/-- **The coatom form after a relabelling**: if, after relabelling the points of `t'` by `σ`, the
root is `g.trans Fin.castSuccEmb`, `P` holds and the first coatom is a closed face, coatom cutoff
determination gives the conclusion of cutoff determination over `t'` along the root
`(g.trans Fin.castSuccEmb).trans σ.toEmbedding`: the castSucc case over `t'.reindex σ`
(`CoatomCutoffDetermination.exists_coface_castSucc`), relabelled back
(`StageType.reindex_extendPerm_symm_mem_cofaces`,
`StageType.IsDeterminedWithin.reindex_extendPerm`). -/
theorem CoatomCutoffDetermination.exists_coface_reindex
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : CoatomCutoffDetermination.{u} P) {K : ℕ} (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) (σ : Equiv.Perm (Fin (k + 1)))
    {g : Fin n ↪ Fin k} (hP : P K (t'.reindex σ) (g.trans Fin.castSuccEmb))
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb (t'.reindex σ) = some p)
    {t : StageType.{u} α n}
    (ht : restrictFace ((g.trans Fin.castSuccEmb).trans σ.toEmbedding) t' = some t)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D' δ) t'
        ((g.trans Fin.castSuccEmb).trans σ.toEmbedding) d := by
  obtain ⟨D'', hD'', δ, hδ, hdet''⟩ := hdet.exists_coface_castSucc hα (ht'.reindex σ) hP hp
    (by rwa [restrictFace_reindex]) hd hdK
  exact ⟨_, reindex_extendPerm_symm_mem_cofaces hD'', δ, hδ, hdet''.reindex_extendPerm⟩

/-- **The hollow coatom form at a root in the first coatom**: the statement of
`CoatomCutoffDetermination.exists_coface_castSucc` without the bound on the top grade. -/
theorem HollowCoatomCutoffDetermination.exists_coface_castSucc
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : HollowCoatomCutoffDetermination.{u} P) (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) {g : Fin n ↪ Fin k}
    (hP : P t' (g.trans Fin.castSuccEmb)) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) :
    ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d := by
  obtain ⟨tb, htb, htbd⟩ := exists_mem_cofaces_restrictFace_eq hα ht' hp ht hd
  obtain ⟨D', hD', -, hrest⟩ := hdet.exists_coface t' g p hα ht' hP hp tb htb d htbd
  exact ⟨D', hD', hrest⟩

/-- **The root in the first coatom after relabelling**: for a legal `t'` with face `t` along a
root `h` that is not onto, some relabelling `σ` of the points of `t'` and some `g` give
`h = g.trans Fin.castSuccEmb` followed by `σ`, with the first coatom of `t'.reindex σ` a closed
face.  The root lies in a closed coatom (`StageType.exists_coatom_trans_eq`), which is the first
coatom after relabelling (`StageType.exists_perm_castSuccEmb_trans`). -/
theorem exists_perm_root_eq {t' : StageType.{u} α (k + 1)} {h : Fin n ↪ Fin (k + 1)}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) (hns : ¬ Function.Surjective h) :
    ∃ (σ : Equiv.Perm (Fin (k + 1))) (g : Fin n ↪ Fin k) (p : StageType.{u} α k),
      (g.trans Fin.castSuccEmb).trans σ.toEmbedding = h ∧
        restrictFace Fin.castSuccEmb (t'.reindex σ) = some p := by
  have hnk : n ≤ k := by
    have hle : n ≤ k + 1 := by simpa using Fintype.card_le_of_embedding h
    refine Nat.le_of_lt_succ (lt_of_le_of_ne hle fun he ↦ hns ?_)
    exact ((Fintype.bijective_iff_injective_and_card h).mpr ⟨h.injective, by simp [he]⟩).2
  obtain ⟨g', f', hg', rfl⟩ :=
    t'.exists_coatom_trans_eq h ((restrictFace_eq_some_iff t' h).mp ht).1 hnk
  obtain ⟨σ, hσ⟩ := exists_perm_castSuccEmb_trans g'
  refine ⟨σ, f', t'.comap g' hg', ?_, ?_⟩
  · rw [Function.Embedding.trans_assoc, hσ]
  · rw [restrictFace_reindex, hσ]
    exact restrictFace_of_mem t' g' hg'

/-- **Cutoff determination from its coatom form**, for a predicate `P` on contexts whose roots are
never onto (`hns`) and which is invariant under relabelling the points of the context, with the
root relabelled along (`hinv`).  The coatom extension property, used for the exact pinned
extension, is compiled (`StageType.hasCoatomExtensions`). -/
theorem CoatomCutoffDetermination.cutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : CoatomCutoffDetermination.{u} P)
    (hns : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → ¬ Function.Surjective h)
    (hinv : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P K t' h → P K (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :
    CutoffDetermination.{u} P where
  exists_coface α K n k t' h hα ht' hP t ht d hd hdK := by
    have hs := hns t' h hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range h := by
        by_contra! hall
        exact hs hall
      exact ⟨k - 1, by have := x.2; omega⟩
    obtain ⟨σ, g, p, rfl, hp⟩ := exists_perm_root_eq ht hs
    have hroot : ((g.trans Fin.castSuccEmb).trans σ.toEmbedding).trans σ.symm.toEmbedding =
        g.trans Fin.castSuccEmb :=
      Function.Embedding.ext fun i ↦ by simp
    have hP' := hinv t' _ σ hP
    rw [hroot] at hP'
    exact hdet.exists_coface_reindex hα ht' σ hP' hp ht hd hdK

/-- **Hollow cutoff determination from its coatom form**, under the hypotheses of
`CoatomCutoffDetermination.cutoffDetermination` on the predicate. -/
theorem HollowCoatomCutoffDetermination.hollowCutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : HollowCoatomCutoffDetermination.{u} P)
    (hns : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P t' h → ¬ Function.Surjective h)
    (hinv : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P t' h → P (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :
    HollowCutoffDetermination.{u} P where
  exists_coface α n k t' h hα ht' hP t ht d hd := by
    have hs := hns t' h hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range h := by
        by_contra! hall
        exact hs hall
      exact ⟨k - 1, by have := x.2; omega⟩
    obtain ⟨σ, g, p, rfl, hp⟩ := exists_perm_root_eq ht hs
    have hroot : ((g.trans Fin.castSuccEmb).trans σ.toEmbedding).trans σ.symm.toEmbedding =
        g.trans Fin.castSuccEmb :=
      Function.Embedding.ext fun i ↦ by simp
    have hP' := hinv t' _ σ hP
    rw [hroot] at hP'
    have ht'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some t := by
      rw [restrictFace_reindex]
      exact ht
    obtain ⟨D'', hD'', δ, hδ, hdet''⟩ := hdet.exists_coface_castSucc hα (ht'.reindex σ) hP' hp
      ht'' hd
    exact ⟨_, reindex_extendPerm_symm_mem_cofaces hD'', δ, hδ, hdet''.reindex_extendPerm⟩

end Realization

end VaughtConjecture

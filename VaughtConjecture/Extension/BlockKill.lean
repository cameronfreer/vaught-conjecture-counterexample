/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.Gluing

/-!
# Killing the cells read below a block

Roadmap, Layer 3, 3.1, (R6); the step of the lift by grades that sets a cap to `⊥`.

A lawful labelling may be set to `⊥` at a set `K` of cells when every cell kept and not `⊥` reads
the cells of `K` (not already `⊥`) in the blocks below some multiple `ω * β` and the other cells at
or above it: the transformation of its locality, preceded by the map killing the labels below
`ω * β`, is again a witness.  Compiled in this repository (theorem named):

* **The block kill** (`Label.blockKill`, `Label.blockKill_visibilityReplace`): the map sending the
  labels below `ω * β` to `⊥` and fixing the others commutes with every visibility replacement
  (replacement keeps the block).
* **Locality after a kill** (`Label.TransformsTo.kill`): at a cell `c` of maximal grade not read
  below `ω * β`, a locality `E ⇒ (d ↦ min (p d) (p c))` gives `E ⇒ (d ↦ min (q d) (q c))` for the
  labelling `q` equal to `⊥` where `E` is below `ω * β` and to `p` elsewhere.
* **The kill keeps lawfulness** (`CellScheme.Rows.IsLawful.kill`): `⊥` on `K`, the labelling
  elsewhere, is lawful when every kept cell not `⊥` reads the cells of `K` exactly as the cells
  below some `ω * β` (up to cells already `⊥`) and availability is served by kept cells.

## Placement

Layer 3, 3.1, under "(R6)" of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset
open scoped Ordinal

namespace Label

variable {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

open Classical in
/-- **The block kill** below `ω * β`: `⊥` below `ω * β`, the identity at and above. -/
noncomputable def blockKill (β : Ordinal.{u}) (x : Label.{u}) : Label.{u} :=
  if x < ((ω * β : Ordinal.{u}) : Label.{u}) then ⊥ else x

theorem blockKill_of_lt {β : Ordinal.{u}} {x : Label.{u}}
    (h : x < ((ω * β : Ordinal.{u}) : Label.{u})) : blockKill β x = ⊥ := ite_eq_left h

theorem blockKill_of_not_lt {β : Ordinal.{u}} {x : Label.{u}}
    (h : ¬ x < ((ω * β : Ordinal.{u}) : Label.{u})) : blockKill β x = x := ite_eq_right h

theorem blockKill_bot (β : Ordinal.{u}) : blockKill β ⊥ = ⊥ := by
  unfold blockKill; split_ifs <;> rfl

theorem monotone_blockKill (β : Ordinal.{u}) : Monotone (blockKill β) := fun x y hxy ↦ by
  unfold blockKill
  split_ifs with hx hy hy
  · exact le_rfl
  · exact bot_le
  · exact absurd (hxy.trans_lt hy) hx
  · exact hxy

/-- **The block kill commutes with every visibility replacement.** -/
theorem blockKill_visibilityReplace (β : Ordinal.{u}) (k i : ℕ) (x : Label.{u}) :
    blockKill β (visibilityReplace k i x) = visibilityReplace k i (blockKill β x) := by
  have hβ : Order.IsSuccPrelimit (ω * β) :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)
  have h := visibilityReplace_lt_iff (k := k) (i := i) (x := x) hβ
  by_cases hx : x < ((ω * β : Ordinal.{u}) : Label.{u})
  · rw [blockKill_of_lt (h.mpr hx), blockKill_of_lt hx, visibilityReplace_bot]
  · rw [blockKill_of_not_lt (mt h.mp hx), blockKill_of_not_lt hx]

variable {D : Type*} {grade : D → ℕ}

/-- **Locality after a kill**: at a cell `c` of maximal grade whose label is self-visible at its
grade and whose source is not below `ω * β`, a locality `E ⇒ (d ↦ min (p d) (p c))` gives
`E ⇒ (d ↦ min (q d) (q c))` for any `q` equal to `⊥` where `E` is below `ω * β` and to `p`
elsewhere. -/
theorem TransformsTo.kill {E p q : D → Label.{u}} {c : D} (hmax : ∀ d, grade d ≤ grade c)
    (hvis : IsSelfVisible (grade c) (p c)) (hloc : TransformsTo grade E fun d ↦ min (p d) (p c))
    {β : Ordinal.{u}} (hc : ¬ E c < ((ω * β : Ordinal.{u}) : Label.{u}))
    (hq : ∀ d, q d = if E d < ((ω * β : Ordinal.{u}) : Label.{u}) then ⊥ else p d) :
    TransformsTo grade E fun d ↦ min (q d) (q c) := by
  obtain ⟨τ, hτ, -, hcap⟩ := hloc.exists_isWitness_capped hmax hvis
  have hqc : q c = p c := by rw [hq c, ite_eq_right hc]
  have hρ : IsWitness (stepSuppressor (grade c)) (fun x ↦ τ (blockKill β x)) :=
    ⟨(IsWitness.id_step _).antitone, (IsWitness.id_step _).isSelfVisible,
      by simp [blockKill_bot, hτ.map_bot],
      hτ.monotone.comp (monotone_blockKill β), fun x k hx i hi ↦ by
        rw [blockKill_visibilityReplace, hτ.visibilityReplace_comm _ k hx i hi]⟩
  refine ⟨stepSuppressor (grade c), fun x ↦ τ (blockKill β x), hρ, fun d ↦ ?_⟩
  change min (q d) (q c) = min (τ (blockKill β (E d))) (stepSuppressor (grade c) (grade d))
  rw [stepSuppressor_of_le (hmax d), min_top_right, hqc, hq d]
  split_ifs with hd
  · rw [blockKill_of_lt hd, hτ.map_bot, min_eq_left bot_le]
  · rw [blockKill_of_not_lt hd, hcap]

end Label

namespace CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

open Classical in
/-- **The kill keeps lawfulness.**  Let `p` be lawful and `K` a set of cells.  Suppose that every
cell `e ∉ K` with `p e ≠ ⊥` has a multiple `ω * β` such that every cell `d` below it is in `K` or
`⊥` in `p` exactly where its row reads `d` below `ω * β` (the cells it reads below are in `K` or
`⊥`, the others are not in `K`), and that availability at a kept cell not `⊥` is served by a kept
cell.  Then `⊥` on `K` and `p` elsewhere is lawful. -/
theorem IsLawful.kill {p : ι → Label.{u}} (hp : R.IsLawful p) (K : Set ι)
    (hloc : ∀ e, e ∉ K → p e ≠ ⊥ → ∃ β : Ordinal.{u}, ∀ d : D.below (D.gradedIndex e),
      (R.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∈ K ∨ p d = ⊥) ∧
      (¬ R.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∉ K))
    (havail : ∀ s t, s ∉ K → p s ≠ ⊥ → D.scope s ⊆ D.scope t → D.grade s = D.grade t →
      ∃ u, D.gradedIndex u = D.gradedIndex t ∧ u ∉ K ∧ p s ≤ p u) :
    R.IsLawful fun d ↦ if d ∈ K then ⊥ else p d := by
  classical
  set q : ι → Label.{u} := fun d ↦ if d ∈ K then ⊥ else p d with hqdef
  refine ⟨fun d ↦ ?_, fun e ↦ ?_, fun s t hst hg ↦ ?_⟩
  · by_cases hd : d ∈ K
    · simp only [q, hd, ite_true]; exact isSelfVisible_bot _
    · simp only [q, hd, ite_false]; exact hp.orderly d
  · by_cases hqe : q e = ⊥
    · refine ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ ?_⟩
      simp only at hqe ⊢
      rw [hqe, min_bot_right, min_bot_left]
    have he : e ∉ K := fun h ↦ hqe (by simp only [q, h, ite_true])
    have hpe : p e ≠ ⊥ := fun h ↦ hqe (by simp only [q, he, ite_false, h])
    obtain ⟨β, hβ⟩ := hloc e he hpe
    have hc : ¬ R.row e ⟨e, D.mem_below_gradedIndex e⟩ < ((ω * β : Ordinal.{u}) : Label.{u}) :=
      fun h ↦ ((hβ ⟨e, D.mem_below_gradedIndex e⟩).1 h).elim he hpe
    refine Label.TransformsTo.kill (p := fun d : D.below (D.gradedIndex e) ↦ p d)
      (c := ⟨e, D.mem_below_gradedIndex e⟩) (fun d ↦ d.2.2) (hp.orderly e) (hp.locality e) hc
      fun d ↦ ?_
    by_cases hd : R.row e d < ((ω * β : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left hd]
      rcases (hβ d).1 hd with h | h
      · simp only [q, h, ite_true]
      · simp only [q]; split_ifs <;> simp [h]
    · rw [ite_eq_right hd]
      simp only [q, (hβ d).2 hd, ite_false]
  · by_cases hs : s ∈ K
    · obtain ⟨u, hu, -⟩ := hp.availability s t hst hg
      exact ⟨u, hu, by simp only [q, hs, ite_true]; exact bot_le⟩
    by_cases hps : p s = ⊥
    · obtain ⟨u, hu, -⟩ := hp.availability s t hst hg
      exact ⟨u, hu, by simp only [q, hs, ite_false, hps]; exact bot_le⟩
    obtain ⟨u, hu, huK, hle⟩ := havail s t hs hps hst hg
    exact ⟨u, hu, by simp only [q, hs, huK, ite_false]; exact hle⟩

open Classical in
/-- **The kill keeps lawfulness below a pair** (`CellScheme.Rows.IsLawful.kill`, below `X`). -/
theorem IsLawfulBelow.kill {X : Finset α × ℕ} {p : ι → Label.{u}}
    (hp : R.IsLawfulBelow X fun d ↦ p d) (K : Set ι)
    (hloc : ∀ e ∈ D.below X, e ∉ K → p e ≠ ⊥ → ∃ β : Ordinal.{u},
      ∀ d : D.below (D.gradedIndex e),
        (R.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∈ K ∨ p d = ⊥) ∧
        (¬ R.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∉ K))
    (havail : ∀ s t, t ∈ D.below X → s ∉ K → p s ≠ ⊥ → D.scope s ⊆ D.scope t →
      D.grade s = D.grade t → ∃ u, D.gradedIndex u = D.gradedIndex t ∧ u ∉ K ∧ p s ≤ p u) :
    R.IsLawfulBelow X fun d ↦ if d.1 ∈ K then ⊥ else p d := by
  obtain ⟨hord, hl, hav⟩ := isLawfulBelow_iff_forall.mp hp
  set q : ι → Label.{u} := fun d ↦ if d ∈ K then ⊥ else p d with hqdef
  refine (isLawfulBelow_iff_forall (w := q)).mpr
    ⟨fun d hd ↦ ?_, fun e he ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdK : d ∈ K
    · simp only [q, hdK, ite_true]; exact isSelfVisible_bot _
    · simp only [q, hdK, ite_false]; exact hord d hd
  · by_cases hqe : q e = ⊥
    · refine ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ ?_⟩
      simp only at hqe ⊢
      rw [hqe, min_bot_right, min_bot_left]
    have heK : e ∉ K := fun h ↦ hqe (by simp only [q, h, ite_true])
    have hpe : p e ≠ ⊥ := fun h ↦ hqe (by simp only [q, heK, ite_false, h])
    obtain ⟨β, hβ⟩ := hloc e he heK hpe
    have hc : ¬ R.row e ⟨e, D.mem_below_gradedIndex e⟩ < ((ω * β : Ordinal.{u}) : Label.{u}) :=
      fun h ↦ ((hβ ⟨e, D.mem_below_gradedIndex e⟩).1 h).elim heK hpe
    refine Label.TransformsTo.kill (p := fun d : D.below (D.gradedIndex e) ↦ p d)
      (c := ⟨e, D.mem_below_gradedIndex e⟩) (fun d ↦ d.2.2) (hord e he) (hl e he) hc
      fun d ↦ ?_
    by_cases hd : R.row e d < ((ω * β : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left hd]
      rcases (hβ d).1 hd with h | h
      · simp only [q, h, ite_true]
      · simp only [q]; split_ifs <;> simp [h]
    · rw [ite_eq_right hd]
      simp only [q, (hβ d).2 hd, ite_false]
  · by_cases hs : s ∈ K
    · obtain ⟨u, hu, -⟩ := hav s t ht hst hg
      exact ⟨u, hu, by simp only [q, hs, ite_true]; exact bot_le⟩
    by_cases hps : p s = ⊥
    · obtain ⟨u, hu, -⟩ := hav s t ht hst hg
      exact ⟨u, hu, by simp only [q, hs, ite_false, hps]; exact bot_le⟩
    obtain ⟨u, hu, huK, hle⟩ := havail s t ht hs hps hst hg
    exact ⟨u, hu, by simp only [q, hs, huK, ite_false]; exact hle⟩

end CellScheme.Rows

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedLift

/-!
# A bottom class on the rows bounds the labellings of a bountiful completion

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with a restricted catalogue at the
reading grades; an obstruction to a bottom class on the rows at the reading grade.

Let `F` be a completion below the full grade of a seed, `c` an old cell of grade `k` and `z` an old
cell, and suppose that the row of **every** cell of graded index `(univ, k)` reads `z` or `c` as
`⊥` (as when the rows at the grade `k` are in a bottom class that puts `z` at `⊥`, or have the
cap `c` at `⊥`).

* **Lawful labellings** (`CompletionBelowFullGrade.eq_bot_of_rowState`): every labelling lawful
  below `(univ, k)` that is not `⊥` at `c` is `⊥` at `z`.  Availability at `c` gives a cell `u` of
  `(univ, k)` with a label at least that of `c`; locality at `u` reads `c` and `z` through the row
  of `u`, by a witness fixing `⊥`.
* **Bountifulness** (`CompletionBelowFullGrade.not_exists_coatom_eq_bot`): if `c` and `z` lie below
  a coatom `(C, k)`, no labelling lawful below `(C, k)` in the amalgam is other than `⊥` at both `c`
  and `z`, since the capped lift at `⊥` from `(C, k)` extends it.
* **The lift provision** (`ProfileTower.not_botLiftProvisionOf`): if every splice in the catalogue
  of a predicate `Rw` at `k` is `⊥` at `z` or at `c`, the lift provision at `⊥` fails at every
  profile lawful below the coatom other than `⊥` at `c` and `z` (the orbit code keeps `⊥`).

So, for an admission whose reading rows at the grade `k` are in a bottom class `⊥` at a cell `z`,
or have the cell `c` at `⊥`, with `z` and `c` below a coatom `(C, k)`, a completion whose rows at
`(univ, k)` are such reading rows asks every labelling lawful below `(C, k)` that is not `⊥` at `c`
to be `⊥` at `z`.  A class for which some lawful labelling below `(C, k)` violates this admits no
completion whose rows at `(univ, k)` are in the class.

## Placement

The completion below the full grade with admitted rows at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)

variable {F}

/-- **A bottom class on the rows bounds the lawful labellings.**  If the row of every cell of
graded index `(univ, k)` reads the old cell `z` or the old cell `c` of grade `k` as `⊥`, every
labelling lawful below `(univ, k)` other than `⊥` at `c` is `⊥` at `z`. -/
theorem eq_bot_of_rowState {k : ℕ} {c z : Fin I.amalgam.card}
    (hc : I.amalgam.toCellScheme.grade c = k) (hz : I.amalgam.toCellScheme.grade z ≤ k)
    (hrows : ∀ u, F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) →
      F.rowState u z = ⊥ ∨ F.rowState u c = ⊥)
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) fun w ↦ q w)
    (hqc : q (F.embed c) ≠ ⊥) : q (F.embed z) = ⊥ := by
  obtain ⟨-, hloc, hav⟩ := Rows.isLawfulBelow_iff_forall.mp hq
  have hk0 : 0 < k := hc ▸ I.amalgam.isWellFormed.isWellFormed.grade_pos c
  have hkm : k < m + 2 := hc ▸ I.grade_lt c
  -- A cell of `(univ, k)`.
  obtain ⟨t, ht⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq ((univ : Finset (Fin (m + 2))), k)
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, hk0,
      by simp only [card_univ, Fintype.card_fin]; omega⟩ hkm
  have htb : t ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), k) := by
    rw [CellScheme.mem_below, ht]
  have hst : F.scheme.toCellScheme.scope (F.embed c) ⊆ F.scheme.toCellScheme.scope t := by
    rw [show F.scheme.toCellScheme.scope t = univ from congrArg Prod.fst ht]
    exact subset_univ _
  have hgt : F.scheme.toCellScheme.grade (F.embed c) = F.scheme.toCellScheme.grade t := by
    rw [F.isLowerEmbedding.grade_eq c, hc]
    exact (congrArg Prod.snd ht).symm
  obtain ⟨u, hu, hcu⟩ := hav (F.embed c) t htb hst hgt
  have hu' : F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) := hu.trans ht
  have hqu : q u ≠ ⊥ := fun h ↦ hqc (le_bot_iff.mp (h ▸ hcu))
  obtain ⟨g, σ, hw, heq⟩ := hloc u (by rw [CellScheme.mem_below, hu'])
  -- An old cell of grade at most `k` lies below `u`.
  have hmem {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, F.gradedIndex_embed, hu']
    exact ⟨subset_univ _, hd⟩
  have hread {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ k)
      (h0 : F.rowState u d = ⊥) : min (q (F.embed d)) (q u) = ⊥ := by
    have h := heq ⟨F.embed d, hmem hd⟩
    have hr : F.scheme.rows.row u ⟨F.embed d, hmem hd⟩ = ⊥ := by
      rw [← Scheme.rowAt_of_mem (hmem hd)]
      exact h0
    rw [hr, hw.map_bot, min_bot_left] at h
    exact h
  rcases hrows u hu' with h0 | h0
  · exact (min_eq_bot.mp (hread hz h0)).resolve_right hqu
  · exact absurd ((min_eq_bot.mp (hread hc.le h0)).resolve_right hqu) hqc

/-- **No labelling of a coatom is other than `⊥` at both `c` and `z`** in the amalgam of a seed
with a completion whose rows of full scope at the grade `k` read `z` or `c` as `⊥`, for `c` of
grade `k` and `z` below a coatom `(C, k)`: the capped lift at `⊥` from `(C, k)` would extend it to
a labelling lawful below `(univ, k)` (`CompletionBelowFullGrade.eq_bot_of_rowState`). -/
theorem not_exists_coatom_eq_bot {k : ℕ} {x : Fin (m + 2)}
    (hx : x ∈ (ProfileTower.Pts : Finset (Fin (m + 2)))) {c z : Fin I.amalgam.card}
    (hc : I.amalgam.toCellScheme.grade c = k)
    (hcC : c ∈ I.amalgam.toCellScheme.below (univ.erase x, k))
    (hzC : z ∈ I.amalgam.toCellScheme.below (univ.erase x, k))
    (hrows : ∀ u, F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k) →
      F.rowState u z = ⊥ ∨ F.rowState u c = ⊥)
    {f : I.State} (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, k) fun d ↦ f d)
    (hfc : f c ≠ ⊥) (hfz : f z ≠ ⊥) : False := by
  classical
  have hL := F.isLegalBelowFullGrade
  have hne : univ.erase x ≠ univ := Seed.ne_univ_erase x
  have hk0 : 0 < k := hc ▸ I.amalgam.isWellFormed.isWellFormed.grade_pos c
  have hkm : k ≤ m + 1 := by have := I.grade_lt c; omega
  have hX : (univ.erase x, k) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨F.faces_eq ▸ I.erase_mem_faces hx, hk0, by simp only; rw [Seed.card_erase]; exact hkm⟩
  have hY : ((univ : Finset (Fin (m + 2))), k) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨hL.isWellFormed.univ_mem_faces, hk0, by simp only [card_univ, Fintype.card_fin]; omega⟩
  have hXY : ((univ.erase x, k) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, k) :=
    ⟨erase_subset _ _, le_rfl⟩
  set w : Fin F.scheme.card → Label.{u} := Function.extend F.embed f fun _ ↦ ⊥
  have hwe (d : Fin I.amalgam.card) : w (F.embed d) = f d := F.embed.injective.extend_apply _ _ d
  have hwX : F.scheme.rows.IsLawfulBelow (univ.erase x, k) fun v ↦ w v := by
    rw [F.isLawfulBelow_embed_iff hne]
    simpa only [hwe] using hf
  obtain ⟨q', ⟨hq', -⟩, hq'w⟩ := hL.isBountiful hX hY hXY ⊥ (isSelfVisible_bot k)
    (fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _) ⟨hwX, fun _ ↦ by simp⟩
  set q : Fin F.scheme.card → Label.{u} := Rows.extendBot ((univ : Finset (Fin (m + 2))), k) q'
  have hqq' (v : F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), k)) : q v = q' v :=
    Rows.extendBot_of_mem q' v.2
  have hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) fun v ↦ q v := by
    convert hq' using 1
    exact funext hqq'
  have hold {d : Fin I.amalgam.card} (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, k)) :
      q (F.embed d) = f d := by
    have hdX : F.embed d ∈ F.scheme.toCellScheme.below (univ.erase x, k) := by
      rw [CellScheme.mem_below, F.gradedIndex_embed]
      exact hd
    have h := congrFun hq'w ⟨F.embed d, hdX⟩
    simp only [Function.comp_apply] at h
    rw [← hwe d, ← h, ← hqq']
  have h := eq_bot_of_rowState hc hzC.2 hrows hq (by rw [hold hcC]; exact hfc)
  rw [hold hzC] at h
  exact hfz h

end CompletionBelowFullGrade

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The lift provision at `⊥` fails under a bottom class on the catalogue.**  If every splice of
the catalogue of `Rw` at the grade `k` is `⊥` at `z` or at `c`, then no profile lawful below the
coatom `(univ.erase x, k)` other than `⊥` at `c` and `z` (both below the coatom) has the lift
provision: the orbit code keeps `⊥`. -/
theorem not_botLiftProvisionOf {Rw : I.State → Prop} {k : ℕ} {x : Fin (m + 2)}
    {c z : Fin I.amalgam.card} (hcC : c ∈ I.amalgam.toCellScheme.below (univ.erase x, k))
    (hzC : z ∈ I.amalgam.toCellScheme.below (univ.erase x, k))
    (hcat : ∀ R ∈ rowCat Rw k, hat I k R z = ⊥ ∨ hat I k R c = ⊥)
    {f : I.State} (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, k) fun d ↦ f d)
    (hfc : f c ≠ ⊥) (hfz : f z ≠ ⊥) : ¬ BotLiftProvisionOf Rw k x := fun hprov ↦ by
  obtain ⟨W, -, hWf, hWC⟩ := hprov f hf
  -- The code of `W` is `⊥` exactly where the splice of `W` is.
  have hcode (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, k))
      (h0 : hat I k (code k W) d = ⊥) : f d = ⊥ := by
    rw [hat_of_le hd.2, orbitCode_eq_bot_iff, hat_of_le hd.2, hWf d hd] at h0
    exact h0
  rcases hcat _ hWC with h0 | h0
  · exact hfz (hcode z hzC h0)
  · exact hfc (hcode c hcC h0)

end ProfileTower

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderRanks

/-!
# Rendered tables on the ladder base

Roadmap, Layer 3 ((R3) and (R4), the lift into the full face of grade one of the ladder base).

The **rendering** of a positive table `f` for a member `a` of the ladder base
(`Scheme.render`) reads `f` at the base indices of `a` on the cells of grade one (the old cells of
grade one, at the ranks of `a`, and the ladder points, at their indices for `a`) and is `⊥` above.

* **Rendered tables are lawful** (`Scheme.isLawful_render`): if the table of `a` read by `f` is
  lawful on `S` at grade one, its rendering is a lawful section of the base.  Locality at a ladder
  point is the table lemma of the ladder (`Label.transformsTo_ladderSource`) after capping at the
  index of the point, through the agreement of base indices below the cut
  (`Scheme.baseIndex_agree`); availability is witnessed by the top rung of `a`.
* **Prefix agreement gives capped agreement** (`Scheme.min_render_eq_of_prefix`): if the rank
  vectors of `a` and `b` agree capped at `k`, the tables `f` and `F` agree below `k` and both reach
  the cap `c` at `k`, then the renderings agree capped at `c` at every cell.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

variable (S H prof) in
/-- The **rendering** of the table `f` for the member `a`: `f` at the base indices of `a` on the
cells of grade one, `⊥` above. -/
noncomputable def render (a : Q) (f : ℕ → Label.{u}) (t : Fin (S.card + ladderCard S Q H)) :
    Label.{u} :=
  if (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 then f (baseIndex H prof a t)
  else ⊥

@[simp] theorem render_castAdd (a : Q) (f : ℕ → Label.{u}) (d : Fin S.card) :
    render S H prof a f (Fin.castAdd _ d) =
      if S.toCellScheme.grade d = 1 then f (prof a d) else ⊥ := by
  rw [render, appendFullCellsScheme_grade_castAdd, baseIndex_castAdd]

@[simp] theorem render_natAdd (a : Q) (f : ℕ → Label.{u}) (j : Fin (ladderCard S Q H)) :
    render S H prof a f (Fin.natAdd _ j) = f (baseIndex H prof a (Fin.natAdd _ j)) := by
  rw [render, appendFullCellsScheme_grade_natAdd, ite_eq_left rfl]

/-- **Rendered tables are lawful sections of the base**: for a positive table `f` (monotone, `⊥`
at `0`, self-visible at `1`, positive at `1, …, H`) whose table at the ranks of `a` is lawful on
`S` at grade one, the rendering of `f` for `a` is lawful. -/
theorem isLawful_render {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, IsSelfVisible 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥)
    (hold : S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (prof a d) else ⊥) :
    (ladderBase H prof hS).rows.IsLawful (render S H prof a f) := by
  classical
  refine isLawful_appendFullCells ?_ (fun j ↦ by rw [render_natAdd]; exact hv _)
    (fun i' ↦ ?_) (fun s hs ↦ ?_)
  · -- on the old cells: the table of `a`
    convert hold using 1
    funext d
    simp only [Function.comp_apply, render_castAdd]
  · -- locality at the ladder point `i'`
    set c' := (ladderEquiv S Q H).symm i' with hc'
    set e := baseIndex H prof a (Fin.natAdd _ i') with he
    have hec : e ≤ ladderCeil prof c' := by
      rw [he, baseIndex_natAdd]; exact min_le_right _ _
    have hecut : e ≤ rankCut H (prof a) (prof c'.1) := by
      rw [he, baseIndex_natAdd]; exact min_le_left _ _
    have hmem (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        t.1 ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      refine ⟨subset_univ _, ?_⟩
      have h2 := t.2.2
      simp only [appendFullCellsScheme_gradedIndex_natAdd] at h2
      exact h2
    have hgr (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 :=
      grade_eq_one_of_mem_below hwf (hmem t)
    have htarget : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          min (render S H prof a f t) (render S H prof a f (Fin.natAdd _ i'))) =
        fun t ↦ f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e) := by
      funext t
      rw [render, ite_eq_left (hgr t), render_natAdd, ← he, ← hf.map_min, min_assoc,
        min_eq_right hec, ← min_eq_right hecut, ← min_assoc, baseIndex_agree a c'.1 t.1,
        min_assoc]
    have hsource : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          baseRow H prof i' t.1) =
        fun t ↦ ladderSource (ladderCeil prof c') (baseIndex H prof c'.1 t.1) := by
      funext t
      exact baseRow_of_mem hwf i' (hmem t)
    have hgrade : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t) = fun _ ↦ 1 :=
      funext hgr
    rw [hsource, htarget, hgrade]
    by_cases he0 : e = 0
    · have hz : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e)) =
          fun _ ↦ ⊥ := by
        funext t; rw [he0, Nat.min_zero, h0]
      rw [hz]
      exact TransformsTo.bot _ _
    · exact transformsTo_ladderSource (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            baseIndex H prof c'.1 t.1) (by omega)
        (f := fun k ↦ f (min k e)) (fun _ _ h ↦ hf (min_le_min_right _ h)) (by simp [h0])
        (fun _ ↦ hv _) fun k hk _ ↦ hp _ (by omega) ((min_le_right _ _).trans
          (hecut.trans (rankCut_le H _ _)))
  · -- availability: the top rung of `a` dominates
    have hHl : H - 1 < H := by omega
    refine ⟨ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩), ?_⟩
    rw [render, ite_eq_left hs, render_natAdd, baseIndex_self hprof (a, Sum.inl ⟨H - 1, hHl⟩)]
    exact hf ((baseIndex_le hprof a s).trans (by simp only [ladderCeil, Sum.elim_inl]; omega))

/-- **Prefix agreement gives capped agreement of renderings**: if the rank vectors of `a` and `b`
agree capped at `k ≤ H`, the tables `f` and `F` agree below `k`, and both
are at least `c` at `k`, then the renderings of `f` for `a` and of `F` for `b` agree capped at
`c`. -/
theorem min_render_eq_of_prefix {a b : Q} {k : ℕ} (hkH : k ≤ H)
    (hab : ∀ d, min (prof a d) k = min (prof b d) k) {f F : ℕ → Label.{u}} {c : Label.{u}}
    (hf : Monotone f) (hF : Monotone F) (hlow : ∀ i < k, f i = F i)
    (hfk : c ≤ f k) (hFk : c ≤ F k) (t : Fin (S.card + ladderCard S Q H)) :
    min (render S H prof a f t) c = min (render S H prof b F t) c := by
  -- the base indices of `a` and `b` agree capped at `k`
  have hidx : min (baseIndex H prof a t) k = min (baseIndex H prof b t) k := by
    have h' := congrArg (fun z ↦ min z k) (baseIndex_agree (H := H) (prof := prof) a b t)
    simp only [min_assoc, min_eq_right (le_rankCut hkH hab)] at h'
    exact h'
  unfold render
  split_ifs with ht
  · by_cases hlt : baseIndex H prof a t < k
    · have hb : baseIndex H prof b t = baseIndex H prof a t := by omega
      rw [hb, hlow _ hlt]
    · have hb : k ≤ baseIndex H prof b t := by omega
      rw [min_eq_right (hfk.trans (hf (not_lt.mp hlt))), min_eq_right (hFk.trans (hF hb))]
  · rfl

/-! ### Lawful sections of the base are rendered tables at grade one -/

/-- A cell of the base of graded index `(univ, 1)` is a ladder point. -/
theorem exists_eq_ladder_of_gradedIndex (hS : S.NoFullOne)
    {t : Fin (S.card + ladderCard S Q H)}
    (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex t =
      ((univ : Finset (Fin n)), 1)) :
    ∃ p, t = Fin.natAdd _ (ladderEquiv S Q H p) := by
  induction t using Fin.addCases with
  | left d =>
    rw [appendFullCellsScheme_gradedIndex_castAdd] at ht
    exact absurd ht.ge (hS d)
  | right j => exact ⟨(ladderEquiv S Q H).symm j, by rw [Equiv.apply_symm_apply]⟩

/-- **Every lawful section of the base is a rendered table at grade one**: it is `⊥` at every cell
of grade one, or for the member `b` with the largest top rung it reads a positive table `F` at the
base indices of `b` at every cell of grade one, the old cells included.  The table is the chart of
the top rung of `b` on the codes; availability puts every cell of grade one below that top
rung. -/
theorem exists_render_of_isLawful [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H) {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (ladderBase H prof hS).rows.IsLawful v) :
    (∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 → v t = ⊥) ∨
      ∃ (b : Q) (F : ℕ → Label.{u}), Monotone F ∧ F 0 = ⊥ ∧ (∀ i, IsSelfVisible 1 (F i)) ∧
        (∀ i, 0 < i → i ≤ H → F i ≠ ⊥) ∧
        ∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 →
          v t = F (baseIndex H prof b t) := by
  classical
  have hHl : H - 1 < H := by omega
  set top : Q → Fin (S.card + ladderCard S Q H) := fun b ↦
    Fin.natAdd _ (ladderEquiv S Q H (b, Sum.inl ⟨H - 1, hHl⟩)) with htop
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (fun b ↦ v (top b))
    Finset.univ_nonempty
  have hL := ladderLawful_of_isLawful hwf hv
  -- every cell of grade one lies below the top rung of `b`
  have hlad (p : LadderPt S Q H) : v (Fin.natAdd _ (ladderEquiv S Q H p)) ≤ v (top b) :=
    (hL.le_top (ladderCeil_le hprof) (fun a ↦ (a, Sum.inl ⟨H - 1, hHl⟩)) (fun _ ↦ rfl)
      (fun _ ↦ by simp only [ladderCeil, Sum.elim_inl]; omega) p).trans (hb _ (mem_univ _))
  have hgtop : (S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (top b) =
      ((univ : Finset (Fin n)), 1) := appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hdom (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) : v t ≤ v (top b) := by
    obtain ⟨u, hu, hle⟩ := hv.availability t (top b)
      (by rw [show (S.appendFullCellsScheme 1 (ladderCard S Q H)).scope (top b) = univ from
        congrArg Prod.fst hgtop]; exact subset_univ _)
      (by rw [ht, show (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (top b) = 1 from
        congrArg Prod.snd hgtop])
    obtain ⟨p, rfl⟩ := exists_eq_ladder_of_gradedIndex hS (hu.trans hgtop)
    exact hle.trans (hlad p)
  by_cases h0 : v (top b) = ⊥
  · exact Or.inl fun t ht ↦ le_bot_iff.mp (h0 ▸ hdom t ht)
  right
  obtain ⟨g, σ, hw, heq⟩ := hv.locality (top b)
  set F : ℕ → Label.{u} := fun i ↦ min (σ (ladderSource H i)) (g 1) with hF
  have hmemb (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      t ∈ (ladderBase H prof hS).toCellScheme.below
        ((ladderBase H prof hS).toCellScheme.gradedIndex (top b)) := by
    change _ ≤ (S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (top b)
    rw [hgtop]
    exact ⟨subset_univ _, ht.le⟩
  have hval (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      v t = F (baseIndex H prof b t) := by
    have h := heq ⟨t, hmemb t ht⟩
    simp only at h
    rw [min_eq_left (hdom t ht)] at h
    have hrow := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
      (r := baseRow H prof) (h := hS) (ladderEquiv S Q H (b, Sum.inl ⟨H - 1, hHl⟩))
      ⟨t, hmemb t ht⟩
    have ht1 : t ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) :=
      ⟨subset_univ _, ht.le⟩
    rw [baseRow_of_mem hwf _ ht1, Equiv.symm_apply_apply] at hrow
    have hc : ladderCeil prof ((b, Sum.inl ⟨H - 1, hHl⟩) : LadderPt S Q H) = H := by
      simp only [ladderCeil, Sum.elim_inl]; omega
    rw [hc] at hrow
    rw [h, hF]
    simp only
    rw [← hrow]
    exact congrArg _ (congrArg g ht)
  -- the rungs of `b`
  have hrung (j : ℕ) (hj : j < H) :
      v (Fin.natAdd _ (ladderEquiv S Q H (b, Sum.inl ⟨j, hj⟩))) = F (j + 1) := by
    have hs := baseIndex_self hprof (b, Sum.inl ⟨j, hj⟩)
    simp only [ladderCeil, Sum.elim_inl] at hs
    rw [hval _ (appendFullCellsScheme_grade_natAdd _ _ _ _), hs]
  have hFmin (i : ℕ) : F (min i H) = F i := by
    simp only [hF, ladderSource_min]
  -- the rungs of `b` are positive
  obtain ⟨-, -, -, -, hrefl⟩ : ∃ (g' : ℕ → Label.{u}) (σ' : Label.{u} → Label.{u}),
      IsWitness g' σ' ∧ _ ∧ _ := hL.reflects hH (ladderCeil_le hprof) b
      (fun i ↦ (b, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ ↦ rfl)
      (fun i hi ↦ by simp only [ladderCeil, Sum.elim_inl]; omega) (by
        have hfin : (⟨min (H - 1) (H - 1), by omega⟩ : Fin H) = ⟨H - 1, hHl⟩ :=
          Fin.ext (min_self _)
        simp only [hfin]
        exact h0)
  refine ⟨b, F, fun i j hij ↦ min_le_min_right _ (hw.monotone (monotone_ladderSource H hij)),
    by simp only [hF, ladderSource_zero, hw.map_bot, min_eq_left bot_le], fun i ↦ ?_,
    fun i hi hiH ↦ ?_, hval⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [hF, ladderSource_zero, hw.map_bot, min_eq_left bot_le]
      exact isSelfVisible_bot _
    · have hm : min i H - 1 < H := by omega
      rw [← hFmin, show min i H = min i H - 1 + 1 by omega, ← hrung _ hm]
      have h := hv.orderly (Fin.natAdd S.card (ladderEquiv S Q H (b, Sum.inl ⟨_, hm⟩)))
      rwa [appendFullCellsScheme_grade_natAdd] at h
  · have hm : i - 1 < H := by omega
    rw [show i = i - 1 + 1 by omega, ← hrung _ hm]
    intro hz
    have h := (hrefl (b, Sum.inl ⟨i - 1, hm⟩)).not.mpr (by
      have hp := ladderIndex_parent (H := H) (prof := prof) (parent := Prod.fst)
        (ladderCeil_le hprof) ((b, Sum.inl ⟨i - 1, hm⟩) : LadderPt S Q H)
      simp only [ladderCeil, Sum.elim_inl] at hp
      rw [hp]; omega)
    exact h (by simp only [hz, min_eq_left bot_le])

end VaughtConjecture.Scheme

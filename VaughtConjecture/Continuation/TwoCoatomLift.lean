/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLift
import VaughtConjecture.Continuation.StableRecoveryDonorLive

/-!
# The two-coatom lift on the lower layer

WORK FILE (branch `research/work-twolift`).  **`Seed.hasTwoCoatomLift`: every seed on three
points has the two-coatom lift** (`Seed.HasTwoCoatomLift`), at every positive cap self-visible at
`2`, with no further hypothesis.

The proof is the two-face lift at the grade one (`Seed.twoFaceLift_one`, module
`VaughtConjecture.Extension.TwoFaceLift`) with its ambient a lawful labelling of the layer at the
grade `1` rather than a catalogue entry at the grade `2`: that proof uses of the catalogue entry
only its lawfulness, of the cap only `IsSelfVisible 1` and `⊥ < γ`, and of the prescription only
its lawfulness at the grade `1` below each coatom
(`Seed.twoFaceLift_one_of_isLawful`).  The boundary owner-capped lift is the one of that proof:

1. **The serving cell.**  If the ambient stays below the cap below `(univ, 1)` it is its own
   extension.  Otherwise availability gives a new cell `u` of graded index `(univ, 1)` with the
   ambient at least the cap there, and a witness bounded by the grade `1` carries the row `S` of
   `u` to the ambient capped at the cap.
2. **No owner is needed.**  The source cap `h₁` is the least value of `S` on the saturated cells;
   an old cell where the glued prescription exceeds the cap is saturated, so `S` is at least `h₁`
   there, since every value of a row of the layer at the grade `1` is self-visible at `1`.  This
   is the cell serving the glued labelling, kept above the cap.
3. **The aligned encoding** of the glued prescription relative to `S` at `h₁`, lawful below each
   coatom at the grade `1`; **the extension** along `S` (`Scheme.extendsFromBoundary_fieldLayer`);
   **the aligned decoding**, a witness bounded by the grade `1`.

The extension below `(univ, 1)` is then glued with the prescription over the coatoms at the grade
`2` (`CellScheme.Rows.IsLawfulBelow.glue₃`, as in `Seed.exists_isLawfulBelow_of_twoFaceLift`), and
on three points every cell of the lower layer lies below `(univ, 2)`.

So the admitted layer with a donor, both coatoms live at grade `1`, is legal below the full grade
under the raise and the capped exact lift alone (`Seed.isLegalBelowFullGrade_donorLayer_live'`),
and the h2 assembly at two points no longer rests on the two-coatom lift
(`H2.hasTwoCoatomLift_two`, module `VaughtConjecture.Continuation.H2Two`).
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- The rows of the new cells of the layer at the grade `1` are never `⊤`. -/
private theorem rowBelow_ne_top_one' {u : Fin (I.tower 1).card}
    (hu : (I.tower 1).toCellScheme.gradedIndex u = (univ, 1))
    (d : (I.tower 1).toCellScheme.below (univ, 1)) :
    (I.tower 1).rows.rowBelow u hu d ≠ ⊤ := by
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower 0) (k := 1)
    (hS := I.not_univ_succ_le_tower 0) hu
  exact (Scheme.isShort_ne_top_row_fieldLayer (hS := I.not_univ_succ_le_tower 0) i _).2

/-- **The two-face lift at the grade one along a lawful ambient.**  Along every lawful labelling
`a` of the layer at the grade `1`, at every cap `γ` self-visible at `1` with `⊥ < γ`, a labelling
`w` of the amalgam lawful below both coatoms at the grade `1` and agreeing with `a` capped at `γ`
on the old cells of grade `1` extends through the layer at the grade `1`, unchanged at the old
cells of grade `1`, to a labelling lawful below `(univ, 1)` agreeing with `a` capped at `γ`.  The
proof is that of `Seed.twoFaceLift_one`. -/
theorem twoFaceLift_one_of_isLawful {a : Fin (I.tower 1).card → Label.{u}}
    (haL : (I.tower 1).rows.IsLawful a) {γ : Label.{u}} (hγ1 : IsSelfVisible 1 γ)
    (hγbot : ⊥ < γ) (w : Fin I.amalgam.card → Label.{u})
    (hwx : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 1) (fun d ↦ w d))
    (hwy : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 1)
      (fun d ↦ w d))
    (hag1 : ∀ d, I.amalgam.toCellScheme.grade d ≤ 1 →
      min (w d) γ = min (a (I.towerEmbed 1 d)) γ) :
    ∃ r : (I.tower 1).toCellScheme.below (univ, 1) → Label.{u},
      (I.tower 1).rows.IsLawfulBelow (univ, 1) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ 1),
        r ⟨I.towerEmbed 1 d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      ∀ e, min (r e) γ = min (a e) γ := by
  classical
  set q : (I.tower 1).toCellScheme.below (univ, 1) → Label.{u} := fun e ↦ a e with hq_def
  have hq : (I.tower 1).rows.IsLawfulBelow (univ, 1) q := haL.isLawfulBelow _
  have hwf := (I.isWellFormed_tower 1 (by omega)).isWellFormed
  have hgr1 (e : Fin (I.tower 1).card) (he : e ∈ (I.tower 1).toCellScheme.below (univ, 1)) :
      (I.tower 1).toCellScheme.grade e = 1 := le_antisymm he.2 (hwf.grade_pos e)
  by_cases hsat : ∃ e : (I.tower 1).toCellScheme.below (univ, 1), γ ≤ q e
  swap
  · -- The ambient stays below the cap: it is its own extension.
    push Not at hsat
    refine ⟨q, hq, fun d hd ↦ ?_, fun e ↦ rfl⟩
    have hlt : a (I.towerEmbed 1 d) < γ := hsat ⟨I.towerEmbed 1 d, I.towerEmbed_mem_below hd⟩
    have h1 := hag1 d hd
    rw [min_eq_left hlt.le] at h1
    have hwd : w d < γ := by
      by_contra hc
      rw [min_eq_right (not_lt.mp hc)] at h1
      exact hlt.ne h1.symm
    rw [min_eq_left hwd.le] at h1
    exact h1.symm
  obtain ⟨d₀, hd₀⟩ := hsat
  -- The serving cell: a new cell of the layer where the ambient reaches the cap.
  obtain ⟨t, ht⟩ : ∃ t, (I.tower 1).toCellScheme.gradedIndex t = (univ, 1) :=
    I.exists_gradedIndex_eq_univ_tower 0
  obtain ⟨u, hu, hle⟩ := (Rows.isLawfulBelow_iff_forall.mp
    (Rows.isLawfulBelow_extendBot.mpr hq)).2.2 d₀.1 t ht.le
    (d₀.2.1.trans (congrArg Prod.fst ht).ge) ((hgr1 _ d₀.2).trans (congrArg Prod.snd ht).symm)
  have hu' : (I.tower 1).toCellScheme.gradedIndex u = (univ, 1) := hu.trans ht
  rw [Rows.extendBot_of_mem q d₀.2, Rows.extendBot_of_mem q hu'.le] at hle
  obtain ⟨τ, hτ, -, hτS⟩ := Rows.exists_isWitness_rowBelow hu' hq hγ1 (hd₀.trans hle)
  set S := (I.tower 1).rows.rowBelow u hu' with hS_def
  have hSlaw : (I.tower 1).rows.IsLawfulBelow (univ, 1) S :=
    Rows.isLawfulBelow_rowBelow hu' (I.isConsistent_tower 1 u)
  have hSvis (e : (I.tower 1).toCellScheme.below (univ, 1)) : IsSelfVisible 1 (S e) := by
    have h' := (Rows.isLawfulBelow_iff_forall.mp (Rows.isLawfulBelow_extendBot.mpr hSlaw)).1
      e.1 e.2
    rwa [hgr1 _ e.2, Rows.extendBot_of_mem S e.2] at h'
  -- The source cap: the least source value over the saturated cells.
  set sat := (Finset.univ : Finset ((I.tower 1).toCellScheme.below (univ, 1))).filter
    (fun e ↦ τ (S e) = γ) with hsat_def
  have hu_mem : (⟨u, hu'.le⟩ : (I.tower 1).toCellScheme.below (univ, 1)) ∈ sat := by
    rw [hsat_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hS_def, hτS]
    exact min_eq_right (hd₀.trans hle)
  obtain ⟨e₀, he₀, hmin⟩ := sat.exists_min_image S ⟨_, hu_mem⟩
  set h₁ := S e₀ with hh₁_def
  have hτh : τ h₁ = γ := (Finset.mem_filter.mp he₀).2
  have hhbot : ⊥ < h₁ := bot_lt_iff_ne_bot.mpr fun hb ↦ by
    rw [hb, hτ.map_bot] at hτh
    exact hγbot.ne hτh
  have hhvis : IsSelfVisible 1 h₁ := hSvis e₀
  obtain ⟨μ, hμ, hhμ⟩ := exists_isSuccPrelimit_lt (I.rowBelow_ne_top_one' hu' e₀)
  -- The source and the prescription on all cells.
  set S' : Fin (I.tower 1).card → Label.{u} := Rows.extendBot (univ, 1) S with hS'_def
  set P : Fin (I.tower 1).card → Label.{u} :=
    Function.extend (I.towerEmbed 1) w (fun _ ↦ ⊥) with hP_def
  have hP (d : Fin I.amalgam.card) : P (I.towerEmbed 1 d) = w d :=
    (I.towerEmbed 1).injective.extend_apply _ _ _
  set V : Finset Label.{u} := Finset.univ.image w with hV_def
  set f : Fin (I.tower 1).card → Label.{u} := Label.alignedEncode μ V 1 h₁ γ S' P with hf_def
  -- At an old cell of grade one, the source decodes to the prescription capped at `γ`.
  have hτold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      τ (S' (I.towerEmbed 1 d)) = min (w d) γ := by
    rw [hS'_def, Rows.extendBot_of_mem S (I.towerEmbed_mem_below hd), hS_def, hτS, hag1 d hd]
  -- The cells below either coatom at the grade one are old.
  have hold (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1)) :
      ∃ d, ∃ hd : I.amalgam.toCellScheme.grade d ≤ 1, I.towerEmbed 1 d = e := by
    have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hsu ↦ he.elim
      (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hsu.ge.trans h'.1)))
      fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hsu.ge.trans h'.1))
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
    refine ⟨d, ?_, rfl⟩
    have h2 : (I.tower 1).toCellScheme.grade (I.towerEmbed 1 d) ≤ 1 := he.elim (·.2) (·.2)
    rwa [grade_towerEmbed] at h2
  -- The alignment: a prescription above the cap sits on a saturated cell.
  have halign (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1))
      (hpe : γ < P e) : h₁ ≤ S' e := by
    obtain ⟨d, hd, rfl⟩ := hold e he
    rw [hP] at hpe
    have hsd : τ (S' (I.towerEmbed 1 d)) = γ := by rw [hτold d hd, min_eq_right hpe.le]
    have hmem := I.towerEmbed_mem_below hd
    rw [hS'_def, Rows.extendBot_of_mem S hmem] at hsd ⊢
    exact hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsd⟩)
  -- The aligned encoding is lawful below each coatom at the grade one.
  have hS'law : (I.tower 1).rows.IsLawfulBelow (univ, 1) fun e ↦ S' e :=
    Rows.isLawfulBelow_extendBot.mpr hSlaw
  have hfX (x : Fin (m + 2))
      (hwX : I.amalgam.rows.IsLawfulBelow (univ.erase x, 1) fun d ↦ w d)
      (hcov : ∀ e, e ∈ (I.tower 1).toCellScheme.below (univ.erase x, 1) →
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
          e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 1)) :
      (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ f e := by
    have hsX : (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ S' e :=
      hS'law.mono (X := (univ.erase x, 1)) ⟨subset_univ _, le_rfl⟩
    have hpX : (I.tower 1).rows.IsLawfulBelow (univ.erase x, 1) fun e ↦ P e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
      simp only [hP]
      exact hwX
    exact Rows.IsLawfulBelow.alignedEncode (V := V) hsX hpX (fun d ↦ d.2.2) hhvis hhbot.ne' hγ1
      hμ hhμ fun e hpe ↦ halign e (hcov e e.2) hpe
  have hfC := hfX (Fin.last (m + 1)) hwx fun e he ↦ .inl he
  have hfD := hfX (Fin.castSucc (Fin.last m)) hwy fun e he ↦ .inr he
  -- The extension through the layer at the grade one along the row of the serving cell.
  have hnot (z : Fin (m + 2)) : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ (univ.erase z, 1) :=
    fun h ↦ ne_univ_erase z (univ_subset_iff.mp h.1)
  have hcover (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.last (m + 1)), 1) ∨
        I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.castSucc (Fin.last m)), 1) :=
    (I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun h ↦ ⟨h, hd⟩) fun h ↦ ⟨h, hd⟩
  have hpos (d : Fin I.amalgam.card) : 1 ≤ I.amalgam.toCellScheme.grade d :=
    (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).2.1
  have hext : (I.tower 1).rows.ExtendsFromBoundary (univ.erase (Fin.last (m + 1)), 1)
      (univ.erase (Fin.castSucc (Fin.last m)), 1) (univ, 1) h₁ S :=
    Scheme.extendsFromBoundary_fieldLayer (S := I.tower 0) (k := 1)
      (hS := I.not_univ_succ_le_tower 0) (fun d hd ↦ le_antisymm hd (hpos d)) (hnot _) (hnot _)
      hcover hu' hhvis hhbot
  obtain ⟨r', hr', hr'f, hr'S⟩ := hext f hfC hfD fun d hd ↦ by
    rw [hf_def, min_alignedEncode hhμ (halign d.1 hd), hS'_def, Rows.extendBot_of_mem S d.2]
  -- Decoding.
  set ρ := alignedDecode μ V 1 τ γ with hρ_def
  have hρ : IsWitness (stepSuppressor.{u} 1) ρ := isWitness_alignedDecode hμ hτ hγ1
  have hamb (d : (I.tower 1).toCellScheme.below (univ, 1)) : min (ρ (r' d)) γ = min (q d) γ := by
    rw [hρ_def, min_alignedDecode_eq hτ.monotone le_rfl hτh.ge hhμ (hr'S d), hS_def, hτS d,
      min_assoc, min_self]
  refine ⟨ρ ∘ r', hr'.map_of_min_eq hq (fun d ↦ d.2.2) hρ hγbot.ne' hamb, fun d hd ↦ ?_, hamb⟩
  have hb : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 1) ∨
      I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last m)), 1) :=
    (I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
      fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩
  rw [Function.comp_apply, hr'f _ hb, hf_def, hρ_def]
  rw [alignedDecode_alignedEncode hτ.monotone hhμ hτh.ge ?_ ?_, hP]
  · rw [hτold d hd, hP, min_assoc, min_self]
  · intro _
    rw [hP]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

/-- **The two-coatom lift at the grade two along a lawful ambient.**  Along every lawful labelling
`a` of the layer at the grade `1`, at every cap `h` self-visible at `2` with `⊥ < h`, a labelling
`w` of that layer lawful below both coatoms at the grade `2` and agreeing with `a` capped at `h`
on their cells is, after a change at the new cells only, lawful below `(univ, 2)` and agrees with
`a` capped at `h` there.  As `Seed.exists_isLawfulBelow_of_twoFaceLift` at `j = 1`, through
`Seed.twoFaceLift_one_of_isLawful`. -/
theorem exists_isLawfulBelow_two_of_isLawful {a : Fin (I.tower 1).card → Label.{u}}
    (haL : (I.tower 1).rows.IsLawful a) {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbot : ⊥ < h)
    {w : Fin (I.tower 1).card → Label.{u}}
    (hwx : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 2) fun e ↦ w e)
    (hwy : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 2)
      fun e ↦ w e)
    (hag : ∀ e, e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
      e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2) →
        min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower 1).card → Label.{u},
      (I.tower 1).rows.IsLawfulBelow (univ, 2) (fun e ↦ g e) ∧
      (∀ e, e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2) →
          g e = w e) ∧
      ∀ e ∈ (I.tower 1).toCellScheme.below (univ, 2), min (g e) h = min (a e) h := by
  classical
  have hx : Fin.last (m + 1) ∈
      ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))) :=
    mem_insert_self _ _
  have hy : Fin.castSucc (Fin.last m) ∈
      ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))) :=
    mem_insert_of_mem (mem_singleton_self _)
  have hxy : Fin.last (m + 1) ≠ Fin.castSucc (Fin.last m) := last_ne_castSucc
  have hwx₀ := (I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase _)).mp hwx
  have hwy₀ := (I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase _)).mp hwy
  have hag₀ (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      min (w (I.towerEmbed 1 d)) h = min (a (I.towerEmbed 1 d)) h :=
    hag _ ((I.scope_subset_or hx hy hxy d).imp
      (fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, Nat.le_succ_of_le hd⟩)
      fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, Nat.le_succ_of_le hd⟩)
  obtain ⟨r, hr, hrw, hra⟩ := I.twoFaceLift_one_of_isLawful haL (hh.mono (by omega)) hbot
    (fun d ↦ w (I.towerEmbed 1 d))
    (by exact hwx₀.mono (X := (univ.erase _, 1)) ⟨subset_rfl, by omega⟩)
    (by exact hwy₀.mono (X := (univ.erase _, 1)) ⟨subset_rfl, by omega⟩) hag₀
  -- The glued labelling: the two-face lift below `(univ, 1)`, `w` elsewhere.
  obtain ⟨g, hgr, hgw⟩ : ∃ g : Fin (I.tower 1).card → Label.{u},
      (∀ e (he : e ∈ (I.tower 1).toCellScheme.below (univ, 1)), g e = r ⟨e, he⟩) ∧
      ∀ e, e ∉ (I.tower 1).toCellScheme.below (univ, 1) → g e = w e :=
    ⟨fun e ↦ if he : e ∈ (I.tower 1).toCellScheme.below (univ, 1) then r ⟨e, he⟩ else w e,
      fun e he ↦ dite_eq_left he, fun e he ↦ dite_eq_right he⟩
  have hgb (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2)) :
      g e = w e := by
    by_cases hej : e ∈ (I.tower 1).toCellScheme.below (univ, 1)
    · rw [hgr e hej]
      have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hu ↦ he.elim
        (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1)))
        fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1))
      obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
      exact hrw d ((I.grade_towerEmbed 1 d).symm.trans_le hej.2)
    · exact hgw e hej
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last (m + 1)), 1 + 1))
    (V := (univ, 1)) (W := (univ.erase (Fin.castSucc (Fin.last m)), 1 + 1)) ?_ ?_ ?_
    (I.mem_below_cover_tower hx hy hxy), hgb, fun e he ↦ ?_⟩
  · convert hwx using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hr using 1
    exact funext fun e ↦ hgr e e.2
  · convert hwy using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · rcases I.mem_below_cover_tower hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgr e hb]
      exact hra _
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)

end VaughtConjecture.Seed

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}}

/-- **The two-coatom lift holds for every seed on three points.**  At every positive cap `h`
self-visible at `2`, lawful labellings `sT` and `sD` of the two coatom types agreeing at the cells
of the common face, both agreeing capped at `h` with the copies of a lawful labelling `a` of the
lower layer, extend to a lawful labelling of the lower layer equal to `sT` and `sD` on the copies
and agreeing with `a` capped at `h` everywhere: glue `sT` and `sD` on the amalgam
(`Seed.exists_isLawful_glue₂`), carry the gluing to the old cells of the lower layer, and apply
`Seed.exists_isLawfulBelow_two_of_isLawful`; every cell of the lower layer lies below
`(univ, 2)`. -/
theorem hasTwoCoatomLift (I : Seed.{u} α 1) : I.HasTwoCoatomLift := by
  classical
  intro h hh hbot sT sD hsT hsD hroot a ha hT hD
  obtain ⟨w, hw, hwL, hwR⟩ := exists_isLawful_glue₂ hsT hsD hroot
  set W₀ : Fin (I.tower 1).card → Label.{u} :=
    Function.extend (I.towerEmbed 1) w (fun _ ↦ ⊥) with hW₀_def
  have hWe (d : Fin I.amalgam.card) : W₀ (I.towerEmbed 1 d) = w d :=
    (I.towerEmbed 1).injective.extend_apply _ _ _
  have hWx : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) fun e ↦ W₀ e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]
    simpa only [hWe] using hw.isLawfulBelow (univ.erase (Fin.last 2), 2)
  have hWy : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      fun e ↦ W₀ e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]
    simpa only [hWe] using hw.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
  -- The old cells agree with the ambient capped at `h`: each is a copy of a cell of a coatom.
  have hold (d : Fin I.amalgam.card) : min (w d) h = min (a (I.towerEmbed 1 d)) h := by
    rcases I.mem_visibleCells_or d with hd | hd
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) hd
      change min (w (StageType.faceCell I.restrictFace_left z)) h = min (a (I.privCell z)) h
      rw [hwL, hT]
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) hd
      change min (w (StageType.faceCell I.restrictFace_right z)) h = min (a (I.donCell z)) h
      rw [hwR, hD]
  have hag (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last 2), 2) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2)) :
      min (W₀ e) h = min (a e) h := by
    have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hu ↦ he.elim
      (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1)))
      fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1))
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
    rw [hWe]
    exact hold d
  obtain ⟨g, hg, hgw, hga⟩ := I.exists_isLawfulBelow_two_of_isLawful ha hh hbot hWx hWy hag
  have hall (e : Fin (I.tower 1).card) : e ∈ (I.tower 1).toCellScheme.below (univ, 2) :=
    ⟨subset_univ _, I.lowerFieldLayer_grade_le e⟩
  have hcopy (d : Fin I.amalgam.card) : g (I.towerEmbed 1 d) = w d := by
    rw [hgw _ ((I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, I.grade_le_two d⟩)
      fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, I.grade_le_two d⟩), hWe]
  exact ⟨g, hg.isLawful hall, fun z ↦ (hcopy _).trans (hwL z),
    fun z ↦ (hcopy _).trans (hwR z), fun e ↦ hga e (hall e)⟩

/-- **The admitted completion with a donor, both coatoms live at grade `1`**, with the two-coatom
lift discharged (`Seed.hasTwoCoatomLift`): `Seed.isLegalBelowFullGrade_donorLayer_live` under the
raise and the capped exact lift with root agreement only. -/
theorem isLegalBelowFullGrade_donorLayer_live' {I : Seed.{u} α 1} {c : I.DonorCap}
    (hT : I.left.IsLegal) (hD : I.right.IsLegal) (hb : I.left.toCellScheme.grade c.cap = 2)
    (hraise : c.HasRaiseFromLive) (hexact : c.HasExactLiftLive) :
    (I.donorLayer c).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_donorLayer_live hT hD hb hraise hexact I.hasTwoCoatomLift

end VaughtConjecture.Seed

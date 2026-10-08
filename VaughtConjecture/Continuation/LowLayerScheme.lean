/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowProfile
import VaughtConjecture.Extension.CatalogueLayer

/-!
# The LOW layer scheme

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); semantic contract,
items 3, 4 and 8.

The layer of controllers of the LOW construction [Kni26, §3.3] over an arbitrary scheme: the
catalogue layer of `VaughtConjecture.Extension.CatalogueLayer` with the cutoff as an extra field
(`Scheme.lowLayer = Scheme.catalogueLayer` with the old cells read through `Sum.inl`; the theorems
of this file are its instances).  Let `S` be a scheme on `n` points with
no cell above `(univ, K)`, `G` a finite set of labels, and `C` a finite catalogue of **profiles**,
labellings of the **fields** `Fin S.card ⊕ Unit` (the cells of `S` and one more field, the
cutoff).  The **LOW layer** (`Scheme.lowLayer S K G C hS`) appends to `S` one cell of scope `univ`
and grade `K` for each profile `a` of `C` (`Scheme.lowEntry`), whose row is the **LOW row** of `a`
(`Scheme.lowRow`): `a` on the old cells, and on the new cell of a profile `b` the agreement height
of `a` and `b` in `G` (`Label.agreementHeight`), which compares the cutoffs as well as the
cells.  This is the field row of `VaughtConjecture.Extension.FieldLayer` with the cutoff as an
extra field.

**Rows** (`Scheme.lowRow_castAdd`, `Scheme.lowRow_natAdd`, `Scheme.rowAt_lowLayer_castAdd`,
`Scheme.rowAt_lowLayer_natAdd`): the row of the new cell of `a` reads the old cells of grade at most
`K` at `a` and the new cells at agreement heights; these are the clauses of
`StageType.IsLowLayer`.

**Consistency** (`Scheme.isConsistent_lowLayer`, compiled in this repository).  If `S` is
consistent and every profile of `C` is lawful on the old cells, with values at most a largest
member of `G`, whose members are self-visible at `K` and include `⊥`, then the LOW layer is
consistent: the LOW row of every profile is a lawful section of the layer
(`Scheme.isLawful_lowRow`).  On the old cells it is the profile; at a new cell its locality is the
identity capped at the agreement height, by the ultrametric inequality
(`Scheme.min_lowRow_agreementHeight`); availability at the full face holds at the cell of the
profile itself, read at the largest member of `G`.  The layer is well formed and, when the
profiles and `G` lie below `ω²`, coded (`Scheme.isWellFormed_lowLayer`, `Scheme.isCoded_lowLayer`).
No strong coding of the rows of `S` is used.

**Completeness at the layer** (`Scheme.exists_gradedIndex_eq_lowLayer`): when `C` is nonempty,
`(univ, K)` is the graded index of a cell; below it, the graded faces are those of `S`.

**Extension of a whole old section at a lowered donor top**
(`Scheme.not_isLawfulBelow_lowLayer_of_lowered`, compiled in this repository).  Let every profile
of `C` be LOW and let `a ∈ C` have donor maximum below a cap `c ≤` its cutoff.  No labelling lawful
below `(univ, K)` in the layer reads the owner (of grade `K`) and the lost top above `c`, a donor
top at `c`, the proper donor fields as `a`, and the cell of `a` at least at `c`.  So a lawful
section of all the old cells that keeps the owner and the lost top above `c` and lowers a donor
top to `c` has no extension through the new cells agreeing with the row of `a` capped at `c`.
This is a fact about the rows of the layer, for every coding of its values.  It is **not** a
failure of bountifulness: bountifulness lifts from one graded face `X < (univ, K)`, and no such
face contains both the owner (grade `K`, scope the private face) and a donor top through the new
point (its scope is not in the private face), so a lift may choose the owner and the lost top
itself, at or near the cap.  Over the profile tower the lift is compiled when the donor has a top
of grade `K` (`ProfileTower.Lvl.Good.cappedLift_lowS_seed`), and the completed display carries a
LOW layer (`ProfileTower.isLowLayer_lowDisplay`, in
`VaughtConjecture.Continuation.LowDisplayLayer`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (K : ℕ) (G : Finset Label.{u})
  (C : Finset (Fin S.card ⊕ Unit → Label.{u}))

/-- The profile of the `i`-th new cell (`Scheme.layerEntry`). -/
noncomputable abbrev lowEntry (i : Fin C.card) : Fin S.card ⊕ Unit → Label.{u} :=
  layerEntry C i

theorem lowEntry_mem (i : Fin C.card) : lowEntry S C i ∈ C := layerEntry_mem i

theorem exists_lowEntry_eq {a : Fin S.card ⊕ Unit → Label.{u}} (ha : a ∈ C) :
    ∃ i, lowEntry S C i = a :=
  exists_layerEntry_eq ha

/-- The **LOW row** of a profile `a` (`Scheme.layerRow` with the old cells read through
`Sum.inl`): `a` on the old cells, and on the new cell of a profile `b` the agreement height of `a`
and `b` in `G`. -/
noncomputable abbrev lowRow (a : Fin S.card ⊕ Unit → Label.{u}) :
    Fin (S.card + C.card) → Label.{u} :=
  layerRow S Sum.inl G C a

variable {S G C} in
theorem lowRow_castAdd (a : Fin S.card ⊕ Unit → Label.{u}) (d : Fin S.card) :
    lowRow S G C a (Fin.castAdd _ d) = a (Sum.inl d) :=
  layerRow_castAdd a d

variable {S G C} in
theorem lowRow_natAdd (a : Fin S.card ⊕ Unit → Label.{u}) (j : Fin C.card) :
    lowRow S G C a (Fin.natAdd _ j) = agreementHeight G a (lowEntry S C j) :=
  layerRow_natAdd a j

/-- **The LOW layer**: the catalogue layer (`Scheme.catalogueLayer`) of `C` with the old cells read
through `Sum.inl`, one cell of scope `univ` and grade `K` for each profile of `C`, whose row is the
LOW row of the profile. -/
noncomputable abbrev lowLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.catalogueLayer K Sum.inl G C hS

variable {S K G C} {hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d}

/-- **Two LOW rows agree capped at the agreement height of their profiles**
(`Scheme.min_layerRow_agreementHeight`). -/
theorem min_lowRow_agreementHeight (hG : ⊥ ∈ G) (a b : Fin S.card ⊕ Unit → Label.{u})
    (x : Fin (S.card + C.card)) :
    min (lowRow S G C a x) (agreementHeight G a b) =
      min (lowRow S G C b x) (agreementHeight G a b) :=
  min_layerRow_agreementHeight hG a b x

/-- **The LOW row of a profile is a lawful section of the LOW layer**, for a profile `a` of `C`
lawful on the old cells, when `⊥ ∈ G`, the members of `G` are self-visible at `K`, and some member
`y` of `G` lies above every member of `G` and every value of `a` (`Scheme.isLawful_layerRow`). -/
theorem isLawful_lowRow (hG : ⊥ ∈ G) (hvis : ∀ x ∈ G, IsSelfVisible K x) {y : Label.{u}}
    (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y) {a : Fin S.card ⊕ Unit → Label.{u}} (ha : a ∈ C)
    (hlaw : S.rows.IsLawful fun d ↦ a (Sum.inl d)) (hay : ∀ f, a f ≤ y) :
    (S.lowLayer K G C hS).rows.IsLawful (lowRow S G C a) :=
  isLawful_layerRow hG hvis hy hmax ha hlaw hay

/-- **The LOW layer is consistent**, under the hypotheses of `Scheme.isLawful_lowRow` for every
profile of `C` (`Scheme.isConsistent_catalogueLayer`). -/
theorem isConsistent_lowLayer (hcons : S.rows.IsConsistent) (hG : ⊥ ∈ G)
    (hvis : ∀ x ∈ G, IsSelfVisible K x) {y : Label.{u}} (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y)
    (hC : ∀ a ∈ C, S.rows.IsLawful (fun d ↦ a (Sum.inl d)) ∧ ∀ f, a f ≤ y) :
    (S.lowLayer K G C hS).rows.IsConsistent :=
  isConsistent_catalogueLayer hcons hG hvis hy hmax hC

/-- **The LOW layer is well formed** when `(univ, K)` is a graded face. -/
theorem isWellFormed_lowLayer (hwf : S.IsWellFormed) (hK0 : 0 < K) (hKn : K ≤ n) :
    (S.lowLayer K G C hS).IsWellFormed :=
  isWellFormed_catalogueLayer hwf hK0 hKn

/-- **The LOW layer is coded** when the profiles and `G` lie below `ω ^ 2`. -/
theorem isCoded_lowLayer (hc : S.IsCoded) (hG : ⊥ ∈ G)
    (hGω : ∀ x ∈ G, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hCω : ∀ a ∈ C, ∀ f, a f < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.lowLayer K G C hS).IsCoded :=
  isCoded_catalogueLayer hc hG hGω hCω

/-- **Completeness at the layer**: when `C` is nonempty, `(univ, K)` is the graded index of a
new cell. -/
theorem exists_gradedIndex_eq_lowLayer (hC : C.Nonempty) :
    ∃ s, (S.lowLayer K G C hS).toCellScheme.gradedIndex s = (univ, K) :=
  exists_gradedIndex_eq_catalogueLayer hC

/-- **The LOW layer reads an old cell at the profile**: the new cell of a profile reads every old
cell of grade at most `K` at the profile (`Scheme.rowAt_catalogueLayer_castAdd`). -/
theorem rowAt_lowLayer_castAdd (i : Fin C.card) {d : Fin S.card}
    (hd : S.toCellScheme.grade d ≤ K) :
    (S.lowLayer K G C hS).rowAt (Fin.natAdd S.card i) (Fin.castAdd C.card d) =
      lowEntry S C i (Sum.inl d) :=
  rowAt_catalogueLayer_castAdd i hd

/-- **The LOW layer reads a new cell at the agreement height** of the two profiles. -/
theorem rowAt_lowLayer_natAdd (i j : Fin C.card) :
    (S.lowLayer K G C hS).rowAt (Fin.natAdd S.card i) (Fin.natAdd S.card j) =
      agreementHeight G (lowEntry S C i) (lowEntry S C j) := by
  have hmem : Fin.natAdd S.card j ∈ (S.lowLayer K G C hS).toCellScheme.below
      ((S.lowLayer K G C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [CellScheme.mem_below]
    change (S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card j) ≤
      (S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card i)
    rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
  rw [rowAt_of_mem hmem]
  exact (appendFullCells_row_natAdd (S := S) (k := K) (M := C.card)
    (r := fun i ↦ lowRow S G C (lowEntry S C i)) (h := hS) i _).trans (layerRow_natAdd _ j)

end VaughtConjecture.Scheme

/-! ### Lowering a donor top above the donor maximum -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {K : ℕ} {G : Finset Label.{u}}
  {C : Finset (Fin S.card ⊕ Unit → Label.{u})}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d}

/-- A cell of the LOW layer of graded index `(univ, K)` is new
(`Scheme.exists_eq_natAdd_of_gradedIndex_catalogueLayer`). -/
theorem exists_natAdd_eq_lowLayer {s : Fin (S.lowLayer K G C hS).card}
    (hs : (S.lowLayer K G C hS).toCellScheme.gradedIndex s = (univ, K)) :
    ∃ i, Fin.natAdd S.card i = s := by
  obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer hs
  exact ⟨i, rfl⟩

local notation "𝓛" => Scheme.lowLayer S K G C hS

/-- **No extension of a whole old section with a lowered donor top.**  Let every profile of `C`
be LOW (for proper donor fields `N`, donor tops `T`, owner `o`, lost top `r` and the cutoff),
and let `a ∈ C` with donor maximum below a cap `c ≤ a β`.  Then no labelling `p'` lawful below
`(univ, K)` in the LOW layer reads the owner (of grade `K`) and the lost top strictly above `c`,
a donor top `x` at `c`, the proper donor fields as `a`, and the new cell of `a` at least at `c`.
Availability at the owner gives a new cell `u` read above `c`; locality at `u` reads the old
cells through the profile `e` of `u`.  If `e` is active, it reads `x` at least at the frontier,
above `c`; if not, the agreement height of `e` and `a`, read at least at `c`, is either above the
donor maximum of `a`, where `e` agrees with `a` on the proper donor fields and the cutoff and is
active, or at most it, where `e` reads a proper donor field at least at `c`.  A fact about the rows
of the layer, for every coding.  It is not a failure of bountifulness: no graded face below
`(univ, K)` contains both the owner and a donor top through the new point, so a capped lift from
a graded face may choose the owner and the lost top itself. -/
theorem not_isLawfulBelow_lowLayer_of_lowered {N : Finset (Fin S.card ⊕ Unit)}
    {T : Set (Fin S.card ⊕ Unit)} {o r x : Fin S.card}
    (hC : ∀ e ∈ C, IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) e) (hG : ⊥ ∈ G)
    (hgo : S.toCellScheme.grade o = K) (hgr : S.toCellScheme.grade r ≤ K)
    (hgx : S.toCellScheme.grade x ≤ K) (hxT : Sum.inl x ∈ T)
    (hN : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ S.toCellScheme.grade d ≤ K)
    {i : Fin C.card} {c : Label.{u}} (hM : donorMax N (lowEntry S C i) < c)
    (hcβ : c ≤ lowEntry S C i (Sum.inr ())) {p' : Fin (𝓛).card → Label.{u}}
    (hp' : (𝓛).rows.IsLawfulBelow (univ, K) fun d ↦ p' d)
    (hpo : c < p' (Fin.castAdd C.card o)) (hpr : c < p' (Fin.castAdd C.card r))
    (hpx : p' (Fin.castAdd C.card x) = c)
    (hpN : ∀ d, Sum.inl d ∈ N → p' (Fin.castAdd C.card d) = lowEntry S C i (Sum.inl d))
    (hpi : c ≤ p' (Fin.natAdd S.card i)) : False := by
  set a := lowEntry S C i with ha_def
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hp'
  have hbelow_old {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ K) :
      Fin.castAdd C.card d ∈ (𝓛).toCellScheme.below (univ, K) :=
    ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S K _ d).trans_le hd⟩
  have hbelow_new (j : Fin C.card) : Fin.natAdd S.card j ∈ (𝓛).toCellScheme.below (univ, K) :=
    (appendFullCellsScheme_gradedIndex_natAdd S K _ j).le
  -- availability at the owner: a new cell `u` read at least as the owner
  obtain ⟨u, hu, hou⟩ := havail (Fin.castAdd C.card o) (Fin.natAdd S.card i) (hbelow_new i)
    (by simp) (by simp [hgo])
  rw [appendFullCellsScheme_gradedIndex_natAdd] at hu
  obtain ⟨j, rfl⟩ := exists_natAdd_eq_lowLayer hu
  set e := lowEntry S C j with he_def
  set v := p' (Fin.natAdd S.card j) with hv_def
  have hcv : c < v := hpo.trans_le hou
  -- locality at `u`
  obtain ⟨g, σ, hσ, heq⟩ := hloc _ (hbelow_new j)
  have hmem (y : Fin (𝓛).card) (hy : y ∈ (𝓛).toCellScheme.below (univ, K)) :
      y ∈ (𝓛).toCellScheme.below ((𝓛).toCellScheme.gradedIndex (Fin.natAdd S.card j)) := by
    rw [show (𝓛).toCellScheme.gradedIndex (Fin.natAdd S.card j) = (univ, K) from
      appendFullCellsScheme_gradedIndex_natAdd S K _ j]
    exact hy
  have hread (y : Fin (𝓛).card) (hy : y ∈ (𝓛).toCellScheme.below (univ, K)) :
      min (p' y) v =
        min (σ ((𝓛).rowAt (Fin.natAdd S.card j) y)) (g ((𝓛).toCellScheme.grade y)) := by
    rw [rowAt_of_mem (hmem y hy)]
    exact heq ⟨y, hmem y hy⟩
  have hgK : v ≤ g K := by
    have h := hread _ (hbelow_new j)
    rw [min_self] at h
    have hgr : (𝓛).toCellScheme.grade (Fin.natAdd S.card j) = K :=
      appendFullCellsScheme_grade_natAdd S K _ j
    rw [hgr] at h
    exact h.trans_le (min_le_right _ _)
  have hg (y : Fin (𝓛).card) (hy : y ∈ (𝓛).toCellScheme.below (univ, K)) :
      v ≤ g ((𝓛).toCellScheme.grade y) := hgK.trans (hσ.antitone hy.2)
  -- reading the old cells through `e`
  have hold {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ K) :
      min (p' (Fin.castAdd C.card d)) v = min (σ (e (Sum.inl d))) (g ((𝓛).toCellScheme.grade
        (Fin.castAdd C.card d))) := by
    rw [hread _ (hbelow_old hd), rowAt_lowLayer_castAdd j hd]
  have hlow_exact {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ K)
      (hlt : p' (Fin.castAdd C.card d) < v) : σ (e (Sum.inl d)) = p' (Fin.castAdd C.card d) := by
    have h := hold hd
    rw [min_eq_left hlt.le] at h
    have hgd := hg _ (hbelow_old hd)
    rcases le_total (σ (e (Sum.inl d))) (g ((𝓛).toCellScheme.grade (Fin.castAdd C.card d))) with
      h' | h'
    · rw [min_eq_left h'] at h; exact h.symm
    · rw [min_eq_right h'] at h; exact absurd (h ▸ hlt) (not_lt.mpr hgd)
  have hhigh {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ K)
      (hlt : c < p' (Fin.castAdd C.card d)) : c < σ (e (Sum.inl d)) := by
    have h := hold hd
    have hgd := hg _ (hbelow_old hd)
    by_contra hle
    have h1 : min (σ (e (Sum.inl d))) (g ((𝓛).toCellScheme.grade (Fin.castAdd C.card d))) ≤ c :=
      (min_le_left _ _).trans (not_lt.mp hle)
    rw [← h] at h1
    exact (lt_min hlt hcv).not_ge h1
  have hσx : σ (e (Sum.inl x)) = c := by
    rw [← hpx]; exact hlow_exact hgx (by rw [hpx]; exact hcv)
  have hσo : c < σ (e (Sum.inl o)) := hhigh hgo.le hpo
  have hσr : c < σ (e (Sum.inl r)) := hhigh hgr hpr
  -- the profile `e` is not active
  have hinact : ¬ donorMax N e < e (Sum.inr ()) := by
    intro hact
    have hfx := (le_max_right _ _).trans (hC e (lowEntry_mem S C j) hact _ hxT)
    have hfr : min (e (Sum.inl o)) (e (Sum.inl r)) ≤ frontier K (Sum.inl o) (Sum.inl r) e :=
      min_le_min le_rfl (le_visibilityReplace (by omega) _)
    have := hσ.monotone (hfr.trans hfx)
    rw [hσ.monotone.map_min, hσx] at this
    exact (lt_min hσo hσr).not_ge this
  -- the agreement height of `e` and `a` is read at least at `c`
  have hκ : c ≤ σ (agreementHeight G e a) := by
    have h := hread _ (hbelow_new i)
    rw [rowAt_lowLayer_natAdd] at h
    have h1 : c ≤ min (p' (Fin.natAdd S.card i)) v := le_min hpi hcv.le
    rw [h] at h1
    exact h1.trans (min_le_left _ _)
  have hag := (agreementHeight_spec hG e a).2
  set κ := agreementHeight G e a
  by_cases hMκ : donorMax N a < κ
  · -- `e` agrees with `a` on the proper donor fields and on the cutoff: it is active
    have hNe : ∀ f ∈ N, e f = a f := fun f hf ↦
      eq_of_min_eq_of_lt (hag f).symm ((le_donorMax hf).trans_lt hMκ)
    apply hinact
    rw [donorMax_congr hNe]
    refine lt_of_lt_of_le (lt_min (hM.trans_le hcβ) hMκ) ?_
    rw [← hag (Sum.inr ())]
    exact min_le_left _ _
  · -- `e` reads a proper donor field at least at `κ`, read below `c`
    rcases N.eq_empty_or_nonempty with hNe | hNe
    · rw [donorMax, hNe, sup_empty] at hMκ
      have hκb : κ = ⊥ := le_bot_iff.mp (not_lt.mp hMκ)
      rw [hκb, hσ.map_bot] at hκ
      exact (bot_le.trans_lt ((bot_le.trans_lt hM))).ne' (le_bot_iff.mp hκ) |>.elim
    · obtain ⟨f, hf, hfa⟩ := exists_mem_eq_sup N hNe a
      obtain ⟨d, rfl, hd⟩ := hN f hf
      have hef : κ ≤ e (Sum.inl d) := by
        have h := hag (Sum.inl d)
        have hκa : κ ≤ a (Sum.inl d) := by
          have := not_lt.mp hMκ
          rwa [donorMax, hfa] at this
        rw [min_eq_right hκa] at h
        exact min_eq_right_iff.mp h
      have hpd : p' (Fin.castAdd C.card d) = a (Sum.inl d) := hpN d hf
      have hdc : p' (Fin.castAdd C.card d) < c := by
        rw [hpd]; exact (le_donorMax hf).trans_lt hM
      have h1 := hlow_exact hd (hdc.trans hcv)
      have h2 := hσ.monotone hef
      rw [h1] at h2
      exact (hκ.trans h2).not_gt hdc

end VaughtConjecture.Scheme

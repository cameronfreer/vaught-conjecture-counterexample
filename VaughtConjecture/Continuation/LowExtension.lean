/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowLayerScheme

/-!
# Extension through the LOW layer at a positive cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: bountifulness of the
layer of controllers); semantic contract, items 3, 4 and 8.

The controllers of the LOW construction [Kni26, §3.3] are a field layer whose profiles carry one
more field, the cutoff, and satisfy the LOW clause (`VaughtConjecture.Continuation.LowLayerScheme`).
This file settles the extension through the controllers at a positive cap, the step of a capped
lift into `(univ, K)` that chooses the labels of the controllers once the old cells are labelled,
and isolates the one condition the LOW clause adds to the extension of the canonical field layer
(`Scheme.exists_extension_fieldLayer`).

**The orbit-canonical LOW catalogue** (`Scheme.lowCatalogue`).  For a scheme `S`, a grade `K` and
the designations of the LOW construction (proper donor fields `N`, donor tops `T`, owner `o`, lost
top `r`, cutoff the extra field), the catalogue is the finite set of profiles with values in the
code grid with block bound `2 (N + 1)` (`N` the number of cells), lawful on the old cells, bottom at
the old cells of grade above `K`, fixed by the orbit code at `K`, and LOW.  The LOW layer over it
(`Scheme.lowLayerCat`) takes agreement heights in the grid `Scheme.lowGrid` with block bound
`2 (N + 1) + 2`.  Its rows are lawful (`Scheme.isLawful_lowRow_lowCatalogue`).  The orbit code of a
profile lawful below `(univ, K)` on the old cells, spliced with bottom above `K`, with any cutoff,
lies in the catalogue exactly when it is LOW (`Scheme.orbitCode_lowSplice_mem_lowCatalogue`): the
orbit map is a witness bounded by grade `K` (`Label.IsLowAt.map`).

**Extension at a positive cap** (`Scheme.exists_extension_lowLayer`, compiled in this repository).
Let `p` be lawful below `(univ, K)` in `S`, `a` a catalogue entry, `h` self-visible and short at `K`
with `⊥ < h`, and `p` agree with `a` capped at `h` on the old cells of grade at most `K`.  For a
cutoff `β` agreeing with that of `a` capped at `h` and such that the spliced profile `(p, β)` is
LOW, some labelling lawful below `(univ, K)` in the LOW layer reads `p` on the old cells of grade at
most `K` and agrees with the LOW row of `a` capped at `h` at every cell below `(univ, K)`, the
controllers included.  The proof is that of the canonical field layer, with the cutoff as a field:
the orbit code `b` of `(p, β)` is an entry, relative room makes it agree with `a` capped at `h`,
cutoff included (`Label.min_orbitCode_eq`), the agreement heights of `b` agree with those of `a`
capped at `h` (`Label.min_agreementHeight_eq_of_isShort`), and the LOW row of `b` read by the orbit
decoder at `h` is the extension, lawful by positive-cap transport with the LOW row of `a` as lawful
companion.

**The agreement-height bookkeeping at the controllers** (`Label.agree_of_le_agreementHeight`,
`Scheme.min_lowRow_eq_of_min_eq`).  An extension that agrees with the LOW row of `a` capped at `h`
reads the controller of `a` at least at `h`, so the profile `b` serving it agrees with `a` capped
at `h` on every field, the cutoff included; conversely two profiles agreeing capped at `h ∈ G`
have LOW rows agreeing capped at `h`.  So the cutoff of the serving profile is prescribed capped
at `h` by the anchor of the ambient section, and nothing else is.

**The cutoff and the frontier condition** (`Label.isLowAt_of_min_eq`,
`Label.donorMax_lt_of_min_eq`, `Label.frontier_le_of_min_eq`, compiled in this repository).  Let
`a` be LOW and `u` agree with `a` capped at `h` on every field.  With the cutoff of `u` at most `h`
(for instance `min (a β) h`), `u` is LOW as soon as it satisfies the **frontier condition**: when
its donor maximum is below its cutoff, every donor top is at least its frontier
`min (u o) (R_K (u r))`; the clause `u x ≥ u β` is inherited from `a`.  Conversely, when the donor
maximum of `a` is below `min (a β) h`, every profile agreeing with `a` capped at `h` is active,
whatever its cutoff, so a LOW one satisfies the frontier condition.  Hence the cutoff of the serving
profile cannot be chosen to avoid the frontier: at the tie of donor raising
(`Label.le_or_eq_of_raise`, a donor top left exactly at the cap `h = R_K M`), the LOW clause asks
that the frontier of the old labels be at most `h`.

**Exact remaining condition for the extension** (`Scheme.exists_extension_lowLayer_of_frontier`):
with the cutoff `min (a β) h`, the only hypothesis beyond those of the canonical field layer is the
frontier condition on the old labels `p`.  The steps of a capped lift that label the old cells (the
lowering of the lost top below the cap from the donor coatom,
`StageType.IsSourceGapContextAt.exists_installation_of_le_owner`, and donor raising from the
private coatom, `StageType.IsLowFamily.donorRaisingGap`) are there to make it hold; the extension
from an arbitrary boundary labelling does not hold (`Scheme.not_isLawfulBelow_lowLayer_of_lowered`).

**The capped lift from a face into the layer** (`Scheme.cappedLift_lowLayerCat`, compiled in this
repository).  For a consistent `S`, a face `C` other than `univ` and the lift of `S` from `(C, j)`
to `(univ, j)`, the LOW layer at `j + 1` lifts capped from `(C, j + 1)` to `(univ, j + 1)` as soon
as the labellings lawful below `(C, j + 1)` extend to labellings of `S` lawful below
`(univ, j + 1)`: arbitrarily at the cap `⊥`, and at a positive cap short at `j + 1` along an entry
`a` agreeing with `a` capped at the cap and satisfying the frontier condition (**the LOW step**).
It is the one-grade lift of `VaughtConjecture.Extension.OwnerCappedLift` with the boundary triple
`(C, j + 1)` three times, so that the whole old part of the lift is the LOW step; the two-coatom
triple of the canonical layers asks the extension from every boundary labelling, which fails at
a boundary labelling with a donor top at the cap below a higher frontier
(`Scheme.not_isLawfulBelow_lowLayer_of_lowered`).

**Over a level of the profile tower** (argued, not compiled).  When `S` is a good level at the grade
`j` (`ProfileTower.Lvl.Good`), the LOW step for the catalogue of this file (profiles of all the
cells of `S`) asks a capped lift of `S` from a coatom into `(univ, j + 1)` along an arbitrary
ambient lawful labelling.  Through the level lift at the grade `j`, the cells of grade `j + 1` of
the other coatom are then a union fill over the common face, which fails for a legal seed at the
grade `2` (`UnionFillCounterexample.not_unionFill_seed`); in the other order it is the two-face
lift, which fails too (`TwoFaceLiftCounterexample.not_twoFaceLift_two`).  So over the tower the LOW
layer is to be built as the next layer of the tower is (`ProfileTower.Lvl.next`): profiles on the
amalgam with the cutoff, rows through the section operator; there the LOW step is a statement
about the amalgam alone.  The extension of this file carries over except at one point: the orbit
code of an amalgam profile together with its cutoff, restricted to the amalgam, need not be
orbit-canonical, which the readability of the section operator (`ProfileTower.Lvl.Good.readable`)
asks.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

/-! ### The cutoff and the frontier condition -/

namespace VaughtConjecture.Label

open Finset

variable {X : Type*} {K : ℕ} {N : Finset X} {T : Set X} {o r β : X}

/-- **Agreement capped below the cap keeps the donor maximum**: if `u` and `a` agree capped at `h`
on the proper donor fields and the donor maximum of `u` is below `h`, the two donor maxima are
equal. -/
theorem donorMax_eq_of_min_eq {u a : X → Label.{u}} {h : Label.{u}}
    (hag : ∀ f ∈ N, min (u f) h = min (a f) h) (hM : donorMax N u < h) :
    donorMax N u = donorMax N a :=
  donorMax_congr fun f hf ↦
    (eq_of_min_eq_of_lt (hag f hf) ((le_donorMax (a := u) hf).trans_lt hM)).symm

/-- **Activity is forced by the anchor**: if `u` agrees with `a` capped at `h` on the proper donor
fields and at the cutoff, and the donor maximum of `a` is below `min (a β) h`, then the donor
maximum of `u` is below its cutoff, whatever the cutoff of `u` above `h`. -/
theorem donorMax_lt_of_min_eq {u a : X → Label.{u}} {h : Label.{u}}
    (hag : ∀ f ∈ N, min (u f) h = min (a f) h) (hβ : min (u β) h = min (a β) h)
    (hact : donorMax N a < min (a β) h) : donorMax N u < u β := by
  have hMa : donorMax N a < h := hact.trans_le (min_le_right _ _)
  have hMu : donorMax N u = donorMax N a := by
    symm
    exact donorMax_eq_of_min_eq (fun f hf ↦ (hag f hf).symm) hMa
  rw [hMu]
  exact hact.trans_le (hβ ▸ min_le_left _ _)

/-- **A LOW profile agreeing with an active anchor satisfies the frontier condition**: under
`Label.donorMax_lt_of_min_eq`, a LOW `u` has every donor top at least its frontier.  The cutoff of
`u` cannot be chosen to avoid this. -/
theorem frontier_le_of_min_eq {u a : X → Label.{u}} {h : Label.{u}}
    (hu : IsLowAt K N T o r β u) (hag : ∀ f ∈ N, min (u f) h = min (a f) h)
    (hβ : min (u β) h = min (a β) h) (hact : donorMax N a < min (a β) h) :
    ∀ x ∈ T, frontier K o r u ≤ u x := fun x hx ↦
  (le_max_right _ _).trans (hu (donorMax_lt_of_min_eq hag hβ hact) x hx)

/-- **The frontier condition suffices**: if `a` is LOW, `u` agrees with `a` capped at `h` on every
field, the cutoff of `u` is at most `h`, and every donor top of `u` is at least its frontier when
the donor maximum of `u` is below its cutoff, then `u` is LOW.  The clause `u β ≤ u x` is
inherited from `a`. -/
theorem isLowAt_of_min_eq {u a : X → Label.{u}} {h : Label.{u}} (ha : IsLowAt K N T o r β a)
    (hag : ∀ f, min (u f) h = min (a f) h) (hβh : u β ≤ h)
    (hfr : donorMax N u < u β → ∀ x ∈ T, frontier K o r u ≤ u x) :
    IsLowAt K N T o r β u := by
  intro hact x hx
  refine max_le ?_ (hfr hact x hx)
  have hMu : donorMax N u < h := hact.trans_le hβh
  have hβa : u β ≤ a β := by
    have h1 := hag β
    rw [min_eq_left hβh] at h1
    exact h1 ▸ min_le_left _ _
  have hMa : donorMax N a < a β := by
    rw [← donorMax_eq_of_min_eq (fun f _ ↦ hag f) hMu]
    exact hact.trans_le hβa
  have hax : u β ≤ a x := hβa.trans ((le_max_left _ _).trans (ha hMa x hx))
  calc u β ≤ min (a x) h := le_min hax hβh
    _ = min (u x) h := (hag x).symm
    _ ≤ u x := min_le_left _ _

end VaughtConjecture.Label

/-! ### The orbit-canonical LOW catalogue -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (K : ℕ) (N : Finset (Fin S.card ⊕ Unit))
  (T : Set (Fin S.card ⊕ Unit)) (o r : Fin S.card)

/-- The **LOW grid** at `K`: the grid with block bound `2 (N + 1) + 2`, for `N` cells. -/
noncomputable abbrev lowGrid : Finset Label.{u} := grid K (2 * (S.card + 1) + 2)

open Classical in
/-- The **orbit-canonical LOW catalogue** at `K`: the profiles of the fields (the cells and the
cutoff) with values in the code grid with block bound `2 (N + 1)`, lawful on the old cells, bottom
at the old cells of grade above `K`, fixed by the orbit code at `K`, and LOW. -/
noncomputable def lowCatalogue : Finset (Fin S.card ⊕ Unit → Label.{u}) :=
  {a ∈ Fintype.piFinset fun _ ↦ codeGrid K (2 * (S.card + 1)) |
    S.rows.IsLawful (fun d ↦ a (Sum.inl d)) ∧
      (∀ d, K < S.toCellScheme.grade d → a (Sum.inl d) = ⊥) ∧ orbitCode K a = a ∧
        IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) a}

variable {S K N T o r}

/-- Membership in the LOW catalogue. -/
theorem mem_lowCatalogue {a : Fin S.card ⊕ Unit → Label.{u}} :
    a ∈ S.lowCatalogue K N T o r ↔ S.rows.IsLawful (fun d ↦ a (Sum.inl d)) ∧
      (∀ d, K < S.toCellScheme.grade d → a (Sum.inl d) = ⊥) ∧ orbitCode K a = a ∧
        IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) a := by
  simp only [lowCatalogue, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun f ↦ ?_, h⟩⟩
  rw [← congrFun h.2.2.1 f]
  exact orbitMap_mem_codeGrid (by simp) _

/-- An entry of the LOW catalogue takes its values in the code grid with block bound `2 (N + 1)`.
-/
theorem mem_codeGrid_of_mem_lowCatalogue {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) (f : Fin S.card ⊕ Unit) :
    a f ∈ codeGrid K (2 * (S.card + 1)) := by
  rw [← congrFun (mem_lowCatalogue.mp ha).2.2.1 f]
  exact orbitMap_mem_codeGrid (by simp) _

/-- The LOW grid contains `⊥`. -/
theorem bot_mem_lowGrid : (⊥ : Label.{u}) ∈ S.lowGrid K := bot_mem_grid _ _

/-- The members of the LOW grid and the values of the entries are at most its ceiling. -/
theorem le_ceiling_of_mem_lowCatalogue {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) (f : Fin S.card ⊕ Unit) :
    a f ≤ gridPoint K (2 * (S.card + 1) + 2) :=
  le_gridPoint_of_mem_codeGrid (codeGrid_mono (by omega) (mem_codeGrid_of_mem_lowCatalogue ha f))

variable (S K N T o r) in
/-- **The LOW layer over the orbit-canonical LOW catalogue.** -/
noncomputable abbrev lowLayerCat
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.lowLayer K (S.lowGrid K) (S.lowCatalogue K N T o r) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d}

/-- **The LOW row of an entry of the LOW catalogue is a lawful section of the layer.** -/
theorem isLawful_lowRow_lowCatalogue {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) :
    (S.lowLayerCat K N T o r hS).rows.IsLawful
      (lowRow S (S.lowGrid K) (S.lowCatalogue K N T o r) a) :=
  isLawful_lowRow (bot_mem_grid _ _) (fun _ hx ↦ isSelfVisible_of_mem_grid hx)
    (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) ha
    (mem_lowCatalogue.mp ha).1 (le_ceiling_of_mem_lowCatalogue ha)

/-- **The LOW layer over the LOW catalogue is consistent.** -/
theorem isConsistent_lowLayerCat (hcons : S.rows.IsConsistent) :
    (S.lowLayerCat K N T o r hS).rows.IsConsistent :=
  isConsistent_lowLayer hcons (bot_mem_grid _ _) (fun _ hx ↦ isSelfVisible_of_mem_grid hx)
    (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) fun _ ha ↦
      ⟨(mem_lowCatalogue.mp ha).1, le_ceiling_of_mem_lowCatalogue ha⟩

/-! ### Spliced profiles -/

variable (S K) in
/-- The **spliced profile** of a labelling `p` of the old cells and a cutoff `β`: `p` at the old
cells of grade at most `K`, `⊥` above, and `β` at the cutoff. -/
noncomputable def lowSplice (p : Fin S.card → Label.{u}) (β : Label.{u}) :
    Fin S.card ⊕ Unit → Label.{u} :=
  Sum.elim (S.toCellScheme.splice K (fun _ ↦ ⊥) p) fun _ ↦ β

@[simp] theorem lowSplice_inr (p : Fin S.card → Label.{u}) (β : Label.{u}) (z : Unit) :
    S.lowSplice K p β (Sum.inr z) = β := rfl

theorem lowSplice_inl_of_le (p : Fin S.card → Label.{u}) (β : Label.{u}) {d : Fin S.card}
    (hd : S.toCellScheme.grade d ≤ K) : S.lowSplice K p β (Sum.inl d) = p d := by
  simp only [lowSplice, Sum.elim_inl]
  exact CellScheme.splice_of_le hd

theorem lowSplice_inl_of_lt (p : Fin S.card → Label.{u}) (β : Label.{u}) {d : Fin S.card}
    (hd : K < S.toCellScheme.grade d) : S.lowSplice K p β (Sum.inl d) = ⊥ := by
  simp only [lowSplice, Sum.elim_inl]
  exact CellScheme.splice_of_lt hd

/-- **The orbit code of a LOW spliced profile is an entry of the LOW catalogue**, for `p` lawful
below `(univ, K)`: the orbit map is a witness bounded by grade `K`, so it keeps lawfulness on the
old cells and the LOW clause, and the orbit code is idempotent. -/
theorem orbitCode_lowSplice_mem_lowCatalogue {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, K) fun d ↦ p d) {β : Label.{u}}
    (hlow : IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) (S.lowSplice K p β)) :
    orbitCode K (S.lowSplice K p β) ∈ S.lowCatalogue K N T o r := by
  set t := S.lowSplice K p β with ht
  set s := S.toCellScheme.splice K (fun _ ↦ ⊥) p with hs
  have hts (d : Fin S.card) : t (Sum.inl d) = s d := rfl
  have hbot (d : Fin S.card) (hd : K < S.toCellScheme.grade d) :
      orbitCode K t (Sum.inl d) = ⊥ := by
    rw [orbitCode_eq_bot_iff]
    exact lowSplice_inl_of_lt p β hd
  -- the mapped splice, lawful below `(univ, K)` and bottom above `K`
  set m : Fin S.card → Label.{u} := fun d ↦ orbitMap K t (s d) with hm
  have hml : S.rows.IsLawfulBelow (univ, K) fun d ↦ m d :=
    ((isLawful_splice_bot hp).isLawfulBelow _).map_of_apply_eq_bot (fun d ↦ d.2.2)
      (isWitness_orbitMap K t) fun _ ↦ orbitMap_eq_bot_iff.mp
  have heq : S.toCellScheme.splice K (fun _ ↦ ⊥) m = m := by
    funext d
    by_cases hd : S.toCellScheme.grade d ≤ K
    · exact CellScheme.splice_of_le hd
    · rw [CellScheme.splice_of_lt (not_le.mp hd)]
      exact (hbot d (not_le.mp hd)).symm
  refine mem_lowCatalogue.mpr ⟨?_, hbot, orbitCode_orbitCode, ?_⟩
  · have := isLawful_splice_bot hml
    rw [heq] at this
    exact this
  · exact hlow.map (isWitness_orbitMap K t) (stepSuppressor_of_le le_rfl)

/-! ### The agreement-height bookkeeping at the controllers -/

/-- **Two profiles agreeing capped at a member `h` of the grid have LOW rows agreeing capped at
`h`**: the agreement height of the two profiles is at least `h`. -/
theorem min_lowRow_eq_of_min_eq {G : Finset Label.{u}} {C : Finset (Fin S.card ⊕ Unit → Label.{u})}
    (hG : ⊥ ∈ G) {h : Label.{u}} (hh : h ∈ G) {a b : Fin S.card ⊕ Unit → Label.{u}}
    (hab : ∀ f, min (a f) h = min (b f) h) (x : Fin (S.card + C.card)) :
    min (lowRow S G C a x) h = min (lowRow S G C b x) h := by
  have hle : h ≤ agreementHeight G a b := le_agreementHeight hh hab
  have h1 := min_lowRow_agreementHeight (C := C) hG a b x
  calc min (lowRow S G C a x) h
      = min (min (lowRow S G C a x) (agreementHeight G a b)) h := by
        rw [min_assoc, min_eq_right hle]
    _ = min (lowRow S G C b x) h := by rw [h1, min_assoc, min_eq_right hle]

end VaughtConjecture.Scheme

namespace VaughtConjecture.Label

variable {ι : Type*} [Fintype ι]

/-- **The serving profile agrees with the anchor capped at the cap, cutoff included**: if a
labelling reads the agreement height of `b` and `a` in `G` at least at `h` (the reading of the
controller of `a`, whose own entry is the ceiling), then `b` and `a` agree capped at `h` on every
field. -/
theorem agree_of_le_agreementHeight {G : Finset Label.{u}} (hG : ⊥ ∈ G) {a b : ι → Label.{u}}
    {h : Label.{u}} (hle : h ≤ agreementHeight G b a) (f : ι) : min (b f) h = min (a f) h := by
  have h1 := (agreementHeight_spec hG b a).2 f
  calc min (b f) h = min (min (b f) (agreementHeight G b a)) h := by
        rw [min_assoc, min_eq_right hle]
    _ = min (a f) h := by rw [h1, min_assoc, min_eq_right hle]

end VaughtConjecture.Label

/-! ### Extension at a positive cap -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {K : ℕ} {N : Finset (Fin S.card ⊕ Unit)}
  {T : Set (Fin S.card ⊕ Unit)} {o r : Fin S.card}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d}

local notation "𝓛" => Scheme.lowLayerCat S K N T o r hS
local notation "ρ" => lowRow S (S.lowGrid K) (S.lowCatalogue K N T o r)

/-- An old cell of grade at most `K` lies below `(univ, K)` in the LOW layer. -/
theorem castAdd_mem_below_lowLayerCat {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ K) :
    Fin.castAdd (S.lowCatalogue K N T o r).card d ∈ (𝓛).toCellScheme.below (univ, K) :=
  ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S K _ d).trans_le hd⟩

/-- **Extension through the LOW layer at a positive cap.**  Let `p` be lawful below `(univ, K)`
in `S`, `a` an entry of the LOW catalogue, `h` self-visible and short at `K` with `⊥ < h`, `p`
agreeing with `a` capped at `h` at the old cells of grade at most `K`, and `β` a cutoff agreeing
with that of `a` capped at `h` such that the spliced profile `(p, β)` is LOW.  Some labelling lawful
below `(univ, K)` in the LOW layer reads `p` at the old cells of grade at most `K` and agrees with
the LOW row of `a` capped at `h` at every cell below `(univ, K)`: the LOW row of the orbit code
`b` of `(p, β)`, read by the orbit decoder at `h`. -/
theorem exists_extension_lowLayer {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, K) fun d ↦ p d) {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) {h : Label.{u}} (hh : IsSelfVisible K h)
    (hs : IsShort K h) (hbot : ⊥ < h)
    (hag : ∀ d, S.toCellScheme.grade d ≤ K → min (p d) h = min (a (Sum.inl d)) h)
    {β : Label.{u}} (hβ : min β h = min (a (Sum.inr ())) h)
    (hlow : IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) (S.lowSplice K p β)) :
    ∃ q : (𝓛).toCellScheme.below (univ, K) → Label.{u},
      (𝓛).rows.IsLawfulBelow (univ, K) q ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ K), q ⟨_, castAdd_mem_below_lowLayerCat hd⟩ = p d) ∧
          ∀ x, min (q x) h = min (ρ a x) h := by
  set t := S.lowSplice K p β with ht_def
  set b := orbitCode K t with hb_def
  have hb : b ∈ S.lowCatalogue K N T o r := orbitCode_lowSplice_mem_lowCatalogue hp hlow
  obtain ⟨-, haup, haa, -⟩ := mem_lowCatalogue.mp ha
  -- the spliced profile agrees with `a` capped at `h` on every field, the cutoff included
  have hagt (f : Fin S.card ⊕ Unit) : min (t f) h = min (a f) h := by
    rcases f with d | z
    · by_cases hd : S.toCellScheme.grade d ≤ K
      · rw [ht_def, lowSplice_inl_of_le p β hd]
        exact hag d hd
      · rw [ht_def, lowSplice_inl_of_lt p β (not_le.mp hd), haup d (not_le.mp hd)]
    · exact hβ
  -- relative room, and its transfer to the agreement heights
  have hba (f : Fin S.card ⊕ Unit) : min (b f) h = min (a f) h :=
    min_orbitCode_eq hh hs haa hagt f
  have hrowh (x : Fin (S.card + (S.lowCatalogue K N T o r).card)) :
      min (ρ b x) h = min (ρ a x) h := by
    induction x using Fin.addCases with
    | left d => rw [lowRow_castAdd, lowRow_castAdd]; exact hba _
    | right j =>
      rw [lowRow_natAdd, lowRow_natAdd]
      exact min_agreementHeight_eq_of_isShort hh hs
        (fun f ↦ ⟨codeGrid_mono (by omega) (mem_codeGrid_of_mem_lowCatalogue hb f),
          codeGrid_mono (by omega) (mem_codeGrid_of_mem_lowCatalogue ha f)⟩) hba _
  -- the decoder reads the old cells literally and keeps the cap at the agreement heights
  have hread (f : Fin S.card ⊕ Unit) : orbitDecoder K t h (b f) = t f :=
    orbitDecoder_orbitCode (fun e ↦ (hba e).trans (hagt e).symm) f
  have hcapr (x : Fin (S.card + (S.lowCatalogue K N T o r).card)) :
      min (orbitDecoder K t h (ρ b x)) h = min (ρ a x) h := by
    induction x using Fin.addCases with
    | left d => rw [lowRow_castAdd, lowRow_castAdd, hread]; exact hagt _
    | right j =>
      rw [min_orbitDecoder_eq (by
          rw [lowRow_natAdd]
          exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1)]
      exact hrowh _
  refine ⟨fun x ↦ orbitDecoder K t h (ρ b x), ?_, fun d hd ↦ ?_, fun x ↦ hcapr x.1⟩
  · exact ((isLawful_lowRow_lowCatalogue (hS := hS) hb).isLawfulBelow _).map_of_min_eq
      ((isLawful_lowRow_lowCatalogue (hS := hS) ha).isLawfulBelow _) (fun x ↦ x.2.2)
      (isWitness_orbitDecoder hh hbot.ne') hbot.ne' fun x ↦ hcapr x.1
  · change orbitDecoder K t h (ρ b (Fin.castAdd _ d)) = p d
    rw [lowRow_castAdd, hread, ht_def, lowSplice_inl_of_le p β hd]

/-- **Extension through the LOW layer under the frontier condition.**  Under the hypotheses of
`Scheme.exists_extension_lowLayer` on `p`, `a` and `h`, with the cutoff `min (a β) h`, the only
remaining hypothesis is the **frontier condition** on the old labels: when the donor maximum of the
spliced profile is below `min (a β) h`, every donor top is at least its frontier.  The LOW clause
of the spliced profile then follows from that of `a` (`Label.isLowAt_of_min_eq`). -/
theorem exists_extension_lowLayer_of_frontier {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, K) fun d ↦ p d) {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) {h : Label.{u}} (hh : IsSelfVisible K h)
    (hs : IsShort K h) (hbot : ⊥ < h)
    (hag : ∀ d, S.toCellScheme.grade d ≤ K → min (p d) h = min (a (Sum.inl d)) h)
    (hfr : donorMax N (S.lowSplice K p (min (a (Sum.inr ())) h)) < min (a (Sum.inr ())) h →
      ∀ x ∈ T, frontier K (Sum.inl o) (Sum.inl r) (S.lowSplice K p (min (a (Sum.inr ())) h)) ≤
        S.lowSplice K p (min (a (Sum.inr ())) h) x) :
    ∃ q : (𝓛).toCellScheme.below (univ, K) → Label.{u},
      (𝓛).rows.IsLawfulBelow (univ, K) q ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ K), q ⟨_, castAdd_mem_below_lowLayerCat hd⟩ = p d) ∧
          ∀ x, min (q x) h = min (ρ a x) h := by
  obtain ⟨-, haup, -, hlowa⟩ := mem_lowCatalogue.mp ha
  have hβ : min (min (a (Sum.inr ())) h) h = min (a (Sum.inr ())) h := by
    rw [min_assoc, min_self]
  refine exists_extension_lowLayer hp ha hh hs hbot hag hβ
    (isLowAt_of_min_eq hlowa (fun f ↦ ?_) (min_le_right _ _) hfr)
  rcases f with d | z
  · by_cases hd : S.toCellScheme.grade d ≤ K
    · rw [lowSplice_inl_of_le p _ hd]
      exact hag d hd
    · rw [lowSplice_inl_of_lt p _ (not_le.mp hd), haup d (not_le.mp hd)]
  · exact hβ

/-- **Extension through the LOW layer at the cap `⊥`**: every labelling lawful below `(univ, K)`
in `S` extends, unchanged at the old cells of grade at most `K`, to a labelling lawful below
`(univ, K)` in the LOW layer: the LOW row of the orbit code of the spliced profile with cutoff `⊥`
(inactive, so LOW), read by the orbit decoder at the least grid point. -/
theorem exists_isLawfulBelow_lowLayerCat {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, K) fun d ↦ p d) :
    ∃ q : (𝓛).toCellScheme.below (univ, K) → Label.{u},
      (𝓛).rows.IsLawfulBelow (univ, K) q ∧
        ∀ d (hd : S.toCellScheme.grade d ≤ K), q ⟨_, castAdd_mem_below_lowLayerCat hd⟩ = p d := by
  set t := S.lowSplice K p ⊥ with ht_def
  have hlow : IsLowAt K N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) t := fun hact ↦
    absurd (hact.trans_le (le_of_eq (lowSplice_inr p ⊥ ()))) not_lt_bot
  have hb := orbitCode_lowSplice_mem_lowCatalogue hp hlow
  refine ⟨fun x ↦ orbitDecoder K t (gridPoint K 0) (ρ (orbitCode K t) x),
    ((isLawful_lowRow_lowCatalogue (hS := hS) hb).isLawfulBelow _).map_of_apply_eq_bot
      (fun x ↦ x.2.2) (isWitness_orbitDecoder (isSelfVisible_gridPoint K 0) (gridPoint_ne_bot K 0))
      fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot K 0), fun d hd ↦ ?_⟩
  change orbitDecoder K t (gridPoint K 0) (ρ (orbitCode K t) (Fin.castAdd _ d)) = p d
  rw [lowRow_castAdd, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e), ht_def,
    lowSplice_inl_of_le p ⊥ hd]

/-- **The values of a LOW row lie in the code grid** with block bound `2 (N + 1) + 2`: the entry on
the old cells, grid points on the controllers.  So the LOW rows are short at `K` and never the
formal top. -/
theorem lowRow_mem_codeGrid {a : Fin S.card ⊕ Unit → Label.{u}}
    (ha : a ∈ S.lowCatalogue K N T o r) (x : Fin (S.card + (S.lowCatalogue K N T o r).card)) :
    ρ a x ∈ codeGrid K (2 * (S.card + 1) + 2) := by
  induction x using Fin.addCases with
  | left d =>
    rw [lowRow_castAdd]
    exact codeGrid_mono (by omega) (mem_codeGrid_of_mem_lowCatalogue ha _)
  | right j =>
    rw [lowRow_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

end VaughtConjecture.Scheme

/-! ### The capped lift into the layer from a coatom -/

namespace VaughtConjecture.Scheme

open Finset Label CellScheme

variable {n : ℕ} {S : Scheme.{u} n} {j : ℕ} {N : Finset (Fin S.card ⊕ Unit)}
  {T : Set (Fin S.card ⊕ Unit)} {o r : Fin S.card}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), j + 1) ≤ S.toCellScheme.gradedIndex d}

local notation "𝓛" => Scheme.lowLayerCat S (j + 1) N T o r hS
local notation "ρ" => lowRow S (S.lowGrid (j + 1)) (S.lowCatalogue (j + 1) N T o r)

/-- **The capped lift from a face into the LOW layer reduces to the old cells.**  Let `S` be
consistent, `C` a face other than `univ` with a cell of graded index `(C, j + 1)` in the layer,
the LOW catalogue nonempty, and `S` lift capped from `(C, j)` to `(univ, j)`.  Suppose:

* at the cap `⊥`, every labelling lawful below `(C, j + 1)` in the layer is, on the old cells
  below `(C, j + 1)`, a labelling of `S` lawful below `(univ, j + 1)`;
* (**the LOW step**) at every entry `a` and every cap `h` self-visible and short at `j + 1` with
  `⊥ < h`, every labelling `w` lawful below `(C, j + 1)` in the layer agreeing there with the LOW
  row of `a` capped at `h` is, on the old cells below `(C, j + 1)`, a labelling `p` of `S` lawful
  below `(univ, j + 1)` that agrees with `a` capped at `h` at the old cells of grade at most
  `j + 1` and satisfies the frontier condition at the cutoff `min (a β) h`.

Then the LOW layer lifts capped from `(C, j + 1)` to `(univ, j + 1)`.  This is the one-grade lift
`CellScheme.Rows.cappedLift_of_boundary_short` with the boundary triple `(C, j + 1)` three times:
the extension from the boundary is the labelling of the old cells given by the two hypotheses,
followed by the extension through the controllers (`Scheme.exists_isLawfulBelow_lowLayerCat` at
`⊥`, `Scheme.exists_extension_lowLayer_of_frontier` at a positive cap along the row of a serving
controller); the LOW rows are lawful, short at `j + 1` and never the formal top. -/
theorem cappedLift_lowLayerCat (hcons : S.rows.IsConsistent) {C : Finset (Fin n)}
    (hC : C ≠ univ) (hX : ∃ c, (𝓛).toCellScheme.gradedIndex c = (C, j + 1))
    (hne : (S.lowCatalogue (j + 1) N T o r).Nonempty)
    (hlift : S.rows.CappedLift (X := (C, j)) (Y := ((univ : Finset (Fin n)), j))
      ⟨subset_univ _, le_rfl⟩)
    (hbot : ∀ w : Fin (𝓛).card → Label.{u}, (𝓛).rows.IsLawfulBelow (C, j + 1) (fun d ↦ w d) →
      ∃ p : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (univ, j + 1) (fun d ↦ p d) ∧
        ∀ d, Fin.castAdd _ d ∈ (𝓛).toCellScheme.below (C, j + 1) → p d = w (Fin.castAdd _ d))
    (hstep : ∀ a ∈ S.lowCatalogue (j + 1) N T o r, ∀ h : Label.{u}, IsSelfVisible (j + 1) h →
      IsShort (j + 1) h → ⊥ < h → ∀ w : Fin (𝓛).card → Label.{u},
        (𝓛).rows.IsLawfulBelow (C, j + 1) (fun d ↦ w d) →
        (∀ d ∈ (𝓛).toCellScheme.below (C, j + 1), min (w d) h = min (ρ a d) h) →
        ∃ p : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (univ, j + 1) (fun d ↦ p d) ∧
          (∀ d, Fin.castAdd _ d ∈ (𝓛).toCellScheme.below (C, j + 1) →
            p d = w (Fin.castAdd _ d)) ∧
          (∀ d, S.toCellScheme.grade d ≤ j + 1 → min (p d) h = min (a (Sum.inl d)) h) ∧
          (donorMax N (S.lowSplice (j + 1) p (min (a (Sum.inr ())) h)) <
              min (a (Sum.inr ())) h →
            ∀ x ∈ T, frontier (j + 1) (Sum.inl o) (Sum.inl r)
              (S.lowSplice (j + 1) p (min (a (Sum.inr ())) h)) ≤
                S.lowSplice (j + 1) p (min (a (Sum.inr ())) h) x)) :
    (𝓛).rows.CappedLift (X := (C, j + 1)) (Y := ((univ : Finset (Fin n)), j + 1))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  have hCY : ¬ ((univ : Finset (Fin n)), j + 1) ≤ (C, j + 1) := fun h ↦ hC (univ_subset_iff.mp h.1)
  -- the old cells below `(C, j + 1)`
  have hold {d : Fin (𝓛).card} (hd : d ∈ (𝓛).toCellScheme.below (C, j + 1)) :
      ∃ e : Fin S.card, Fin.castAdd _ e = d ∧ S.toCellScheme.grade e ≤ j + 1 := by
    refine ⟨⟨d, lt_card_of_mem_below hCY hd⟩, rfl, ?_⟩
    have h2 : (S.appendFullCellsScheme (j + 1) (S.lowCatalogue (j + 1) N T o r).card).grade
        (Fin.castAdd _ ⟨d, lt_card_of_mem_below hCY hd⟩) ≤ j + 1 := hd.2
    rwa [appendFullCellsScheme_grade_castAdd] at h2
  -- the lift at the grade `j`, from `S`
  have hlift' : (𝓛).rows.CappedLift (X := (C, j)) (Y := ((univ : Finset (Fin n)), j))
      ⟨subset_univ _, le_rfl⟩ := by
    have hY : ¬ ((univ : Finset (Fin n)), j + 1) ≤ ((univ : Finset (Fin n)), j) :=
      fun h ↦ by have := h.2; simp at this
    have hpre : S.toCellScheme.IsSourcePrefix (𝓛).toCellScheme (Fin.castAdd _)
        ((univ : Finset (Fin n)), j) :=
      ⟨isLowerEmbedding_castAdd (S := S) (j + 1) _
          (fun i ↦ ρ (lowEntry S (S.lowCatalogue (j + 1) N T o r) i)) hS,
        appendFullCellsScheme_scope_castAdd S (j + 1) _,
        fun d hd ↦ ⟨⟨d, lt_card_of_mem_below hY hd⟩, rfl⟩⟩
    rw [← hpre.cappedLift_iff _ le_rfl]
    convert hlift
    exact comap_rows_castAdd (S := S) (k := j + 1)
      (r := fun i ↦ ρ (lowEntry S (S.lowCatalogue (j + 1) N T o r) i)) (h := hS)
  have hle : ((C, j + 1) : Finset (Fin n) × ℕ) ≤ ((univ : Finset (Fin n)), j + 1) :=
    ⟨subset_univ _, le_rfl⟩
  refine Rows.cappedLift_of_boundary_short (U := (C, j + 1)) (V := (C, j + 1)) (O := (C, j + 1))
    (subset_univ _) hX hlift' le_rfl le_rfl le_rfl hle hle (fun _ hd _ ↦ hd)
    (Rows.cappedLift_refl _) (Rows.cappedLift_refl _) ?_ ?_ fun u hu ↦ ?_
  · -- the extension from the boundary at `⊥`
    intro w hw _ _
    obtain ⟨p, hp, hpw⟩ := hbot w hw
    obtain ⟨q, hq, hqp⟩ := exists_isLawfulBelow_lowLayerCat (N := N) (T := T) (o := o) (r := r)
      (hS := hS) hp
    refine ⟨q, hq, fun d hd ↦ ?_, fun _ ↦ by simp⟩
    have hd' : (d : Fin (𝓛).card) ∈ (𝓛).toCellScheme.below (C, j + 1) := hd.elim id id
    obtain ⟨e, he, heg⟩ := hold hd'
    have := hqp e heg
    rw [hpw e (he ▸ hd')] at this
    convert this using 2
    · exact Subtype.ext he.symm
    · exact he.symm
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨i, -⟩ := exists_lowEntry_eq S _ ha
    exact ⟨Fin.natAdd _ i, appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩
  · -- the serving controller and its row
    obtain ⟨i, rfl⟩ := exists_natAdd_eq_lowLayer hu
    set a := lowEntry S (S.lowCatalogue (j + 1) N T o r) i with ha_def
    have ha : a ∈ S.lowCatalogue (j + 1) N T o r := lowEntry_mem S _ i
    have hrowB (d : (𝓛).toCellScheme.below ((univ : Finset (Fin n)), j + 1)) :
        (𝓛).rows.rowBelow _ hu d = ρ a d := by
      exact appendFullCells_row_natAdd (S := S) (k := j + 1)
        (r := fun i ↦ ρ (lowEntry S (S.lowCatalogue (j + 1) N T o r) i)) (h := hS) i _
    refine ⟨isConsistent_lowLayerCat hcons _, fun d ↦ ?_, fun d ↦ ?_, fun h hh hs hb ↦ ?_⟩
    · rw [hrowB]; exact isShort_of_mem_codeGrid (lowRow_mem_codeGrid ha _)
    · rw [hrowB]; exact ne_top_of_mem_codeGrid (lowRow_mem_codeGrid ha _)
    · intro w hw _ hwS
      have hwa (d : Fin (𝓛).card) (hd : d ∈ (𝓛).toCellScheme.below (C, j + 1)) :
          min (w d) h = min (ρ a d) h := by
        have := hwS ⟨d, (𝓛).toCellScheme.below_mono hle hd⟩ (.inl hd)
        rwa [hrowB] at this
      obtain ⟨p, hp, hpw, hpa, hfr⟩ := hstep a ha h hh hs hb w hw hwa
      obtain ⟨q, hq, hqp, hqa⟩ := exists_extension_lowLayer_of_frontier (hS := hS) hp ha hh hs hb
        hpa hfr
      refine ⟨q, hq, fun d hd ↦ ?_, fun d ↦ by rw [hrowB]; exact hqa d⟩
      have hd' : (d : Fin (𝓛).card) ∈ (𝓛).toCellScheme.below (C, j + 1) := hd.elim id id
      obtain ⟨e, he, heg⟩ := hold hd'
      have := hqp e heg
      rw [hpw e (he ▸ hd')] at this
      convert this using 2
      · exact Subtype.ext he.symm
      · exact he.symm

end VaughtConjecture.Scheme

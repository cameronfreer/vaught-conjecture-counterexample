/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTower

/-!
# Source-gap requests: the low clause of a state at a cutoff field

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3).

A *state* is a labelling `s : ι → Label` of a family of cells (in the application, the cells of the
amalgam of a source-gap context and a donor).  **Source-gap requests** (`SourceGapRequests ι`) fix
the **owner** `o` and the **lost top** `r` of the context, the top grade `K`, and two finite sets of
designated donor cells: the cells `Lo` designated below the top, and the designated tops `Tops`.
Write `vR K K` for visibility replacement at threshold `K` with value `K`.

* The **frontier** of `s` (`SourceGapRequests.frontier`) is `min (s o) (vR K K (s r))`.
* The **low maximum** of `s` (`SourceGapRequests.lowMax`) is the maximum of `s` over `Lo` (`⊥`
  when `Lo` is empty).
* The state satisfies the **low clause at the field `b`** (`SourceGapRequests.AdmitsLowAt s b`)
  when, if the low maximum lies below `b`, every designated top is at least `max b (frontier s)`.
* **The existential form** (`SourceGapRequests.AdmitsLow G s`): the low clause at some field in a
  set `G` of labels (a grid).
* **The partner form** (`SourceGapRequests.AdmitsLowVia π s`): the low clause at the field `s π`,
  the value of the state at a cell `π` (the **partner**).

## Results

Each item below is compiled in this file (theorem named).

* **The existential form asks nothing above a grid point at most the low maximum**
  (`SourceGapRequests.admitsLowAt_of_le`, `SourceGapRequests.admitsLow_of_mem_of_le`): the low
  clause holds at every field at most the low maximum, so `AdmitsLow G s` holds as soon as `G`
  has a point at most the low maximum of `s`; with `⊥ ∈ G` it holds for every state.  The field
  must be fixed by the state (the partner form) for the clause to say anything.
* **The bottom cases**: the clause holds at the field `⊥` for every state
  (`SourceGapRequests.admitsLowAt_bot_field`), so the constant `⊥` state satisfies the partner form
  (`SourceGapRequests.admitsLowVia_const_bot`); at a field other than `⊥` the constant `⊥` state
  fails it as soon as `Tops` is nonempty (`SourceGapRequests.not_admitsLowAt_const_bot`).
* **The actual labelling** (`SourceGapRequests.admitsLowAt_of_eq_top`): a state that is `⊤` at
  every designated top satisfies the clause at every field.
* **Capping** (`SourceGapRequests.AdmitsLowAt.cap`, `SourceGapRequests.AdmitsLowVia.cap`): for a
  label `h` self-visible at `K`, the state capped at `h` satisfies the clause at the field capped at
  `h`.
* **Plain images** (`SourceGapRequests.AdmitsLowAt.comp`, `SourceGapRequests.AdmitsLowVia.comp`):
  for a witness bounded by a grade `K' ≥ K` (`IsWitness (stepSuppressor K') σ`), the state `σ ∘ s`
  satisfies the clause at the field `σ b`.  A monotone map fixing `⊥` commutes with the maximum
  over `Lo`, and the shifter commutes with `vR K K` without condition at `K ≤ K'`.
* **The code of a profile** (`SourceGapRequests.AdmitsLowAt.code`,
  `SourceGapRequests.AdmitsLowVia.code`): if the owner, the lost top and the designated cells (and
  the partner) have grade at most `k`, and `K ≤ k`, the code `orbitCode k (hat I k P)` satisfies
  the clause at the orbit map of the field.  The grade bound is needed: the splice sends a
  designated top above `k` to `⊥` and keeps a field above the low maximum, so the clause fails
  (`VaughtConjecture.SourceGapRequestsExamples`).
* **The field is read at the partner** (`SourceGapRequests.apply_eq_of_lt`): if `s'` is the image
  of `s` under a witness `(g, σ)` over the grades `grade`, `d ↦ min (σ (s d)) (g (grade d))`, and
  the partner `π` lies below a cell `ς` (the **separator**) in grade with `s' π < s' ς`, then the
  shifted field `σ (s π)` is `s' π`.  So the field of the image of the partner form is the value of
  the image at the partner, below a separator.
-/

universe u

namespace VaughtConjecture

open Label

/-- **Source-gap requests** on a family of cells `ι`: the owner and the lost top of the context,
the top grade `K`, the designated donor cells below the top, and the designated tops. -/
structure SourceGapRequests (ι : Type*) where
  /-- The owner. -/
  owner : ι
  /-- The lost top. -/
  lost : ι
  /-- The top grade. -/
  K : ℕ
  /-- The designated donor cells below the top. -/
  Lo : Finset ι
  /-- The designated tops. -/
  Tops : Finset ι

namespace SourceGapRequests

variable {ι : Type*} (r : SourceGapRequests ι) {s s' : ι → Label.{u}} {b : Label.{u}}

/-- The **frontier** of a state: the owner, capped at the replacement at `K` of the lost top. -/
noncomputable def frontier (s : ι → Label.{u}) : Label.{u} :=
  min (s r.owner) (visibilityReplace r.K r.K (s r.lost))

/-- The **low maximum** of a state: its maximum over the designated cells below the top. -/
noncomputable def lowMax (s : ι → Label.{u}) : Label.{u} := r.Lo.sup s

/-- **The low clause at the field `b`**: if the low maximum lies below `b`, every designated top is
at least `b` and at least the frontier. -/
def AdmitsLowAt (s : ι → Label.{u}) (b : Label.{u}) : Prop :=
  r.lowMax s < b → ∀ y ∈ r.Tops, max b (r.frontier s) ≤ s y

/-- **The existential form**: the low clause at some field in the set `G`. -/
def AdmitsLow (G : Set Label.{u}) (s : ι → Label.{u}) : Prop :=
  ∃ b ∈ G, r.AdmitsLowAt s b

/-- **The partner form**: the low clause at the value of the state at the partner `π`. -/
def AdmitsLowVia (π : ι) (s : ι → Label.{u}) : Prop :=
  r.AdmitsLowAt s (s π)

variable {r}

/-! ### The existential form, the bottom cases, the actual labelling -/

/-- The low clause holds at every field at most the low maximum. -/
theorem admitsLowAt_of_le (h : b ≤ r.lowMax s) : r.AdmitsLowAt s b :=
  fun hlt ↦ absurd hlt (not_lt.mpr h)

/-- **The existential form asks nothing** when the set has a point at most the low maximum. -/
theorem admitsLow_of_mem_of_le {G : Set Label.{u}} (hb : b ∈ G) (h : b ≤ r.lowMax s) :
    r.AdmitsLow G s :=
  ⟨b, hb, admitsLowAt_of_le h⟩

/-- The low clause holds at the field `⊥`. -/
theorem admitsLowAt_bot_field : r.AdmitsLowAt s ⊥ :=
  admitsLowAt_of_le bot_le

/-- With `⊥` in the set, the existential form holds for every state. -/
theorem admitsLow_of_bot_mem {G : Set Label.{u}} (h : ⊥ ∈ G) : r.AdmitsLow G s :=
  ⟨⊥, h, admitsLowAt_bot_field⟩

variable (r) in
/-- The constant `⊥` state satisfies the partner form. -/
theorem admitsLowVia_const_bot (π : ι) : r.AdmitsLowVia π fun _ ↦ (⊥ : Label.{u}) :=
  admitsLowAt_bot_field

/-- At a field other than `⊥`, the constant `⊥` state fails the low clause when there is a
designated top. -/
theorem not_admitsLowAt_const_bot (hb : b ≠ ⊥) (hT : r.Tops.Nonempty) :
    ¬ r.AdmitsLowAt (fun _ ↦ (⊥ : Label.{u})) b := by
  intro h
  obtain ⟨y, hy⟩ := hT
  have hlow : r.lowMax (fun _ ↦ (⊥ : Label.{u})) = ⊥ := Finset.sup_bot _
  have := h (by rw [hlow]; exact bot_lt_iff_ne_bot.mpr hb) y hy
  exact hb (le_bot_iff.mp ((le_max_left _ _).trans this))

/-- **The actual labelling**: a state `⊤` at every designated top satisfies the low clause at
every field. -/
theorem admitsLowAt_of_eq_top (hT : ∀ y ∈ r.Tops, s y = ⊤) : r.AdmitsLowAt s b :=
  fun _ y hy ↦ by rw [hT y hy]; exact le_top

/-! ### Capping -/

/-- The low maximum of a capped state is the capped low maximum. -/
theorem lowMax_min (h : Label.{u}) : r.lowMax (fun d ↦ min (s d) h) = min (r.lowMax s) h :=
  (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x ↦ min x h)
    (fun _ _ hxy ↦ min_le_min_right h hxy) (min_eq_left bot_le)).symm

/-- The frontier of a capped state, at a cap self-visible at `K`, is the capped frontier. -/
theorem frontier_min {h : Label.{u}} (hh : IsSelfVisible r.K h) :
    r.frontier (fun d ↦ min (s d) h) = min (r.frontier s) h := by
  simp only [frontier]
  rw [visibilityReplace_min_of_isSelfVisible le_rfl hh, min_min_min_comm, min_self]

/-- **Capping keeps the low clause**: for `h` self-visible at `K`, the capped state satisfies the
clause at the capped field. -/
theorem AdmitsLowAt.cap (hs : r.AdmitsLowAt s b) {h : Label.{u}} (hh : IsSelfVisible r.K h) :
    r.AdmitsLowAt (fun d ↦ min (s d) h) (min b h) := by
  intro hlt y hy
  rw [lowMax_min] at hlt
  have hb : r.lowMax s < b := not_le.mp fun hle ↦ (not_lt.mpr (min_le_min_right h hle)) hlt
  rw [frontier_min hh, show max (min b h) (min (r.frontier s) h) =
    min (max b (r.frontier s)) h from (inf_sup_right _ _ _).symm]
  exact min_le_min_right h (hs hb y hy)

/-- **Capping keeps the partner form**, for `h` self-visible at `K`. -/
theorem AdmitsLowVia.cap {π : ι} (hs : r.AdmitsLowVia π s) {h : Label.{u}}
    (hh : IsSelfVisible r.K h) : r.AdmitsLowVia π fun d ↦ min (s d) h :=
  AdmitsLowAt.cap hs hh

/-! ### Plain images -/

section Comp

variable {K' : ℕ} {σ : Label.{u} → Label.{u}}

/-- The low maximum of a plain image is the image of the low maximum. -/
theorem lowMax_comp (hw : IsWitness (stepSuppressor K') σ) :
    r.lowMax (σ ∘ s) = σ (r.lowMax s) :=
  (Finset.apply_sup_eq_sup_comp_of_linearOrder σ hw.monotone hw.map_bot).symm

/-- The frontier of a plain image is the image of the frontier, for `K ≤ K'`. -/
theorem frontier_comp (hw : IsWitness (stepSuppressor K') σ) (hK : r.K ≤ K') :
    r.frontier (σ ∘ s) = σ (r.frontier s) := by
  simp only [frontier, Function.comp_apply]
  rw [hw.monotone.map_min, hw.visibilityReplace_comm _ r.K
    (by rw [stepSuppressor_of_le hK]; exact le_top) r.K le_rfl]

/-- **Plain images keep the low clause**: for a witness bounded by a grade `K' ≥ K`, the image
`σ ∘ s` satisfies the clause at the field `σ b`. -/
theorem AdmitsLowAt.comp (hs : r.AdmitsLowAt s b) (hw : IsWitness (stepSuppressor K') σ)
    (hK : r.K ≤ K') : r.AdmitsLowAt (σ ∘ s) (σ b) := by
  intro hlt y hy
  rw [lowMax_comp hw] at hlt
  have hb : r.lowMax s < b := not_le.mp fun hle ↦ (not_lt.mpr (hw.monotone hle)) hlt
  rw [frontier_comp hw hK, ← hw.monotone.map_max]
  exact hw.monotone (hs hb y hy)

/-- **Plain images keep the partner form**, for a witness bounded by a grade `K' ≥ K`. -/
theorem AdmitsLowVia.comp {π : ι} (hs : r.AdmitsLowVia π s)
    (hw : IsWitness (stepSuppressor K') σ) (hK : r.K ≤ K') : r.AdmitsLowVia π (σ ∘ s) :=
  AdmitsLowAt.comp hs hw hK

end Comp

/-! ### Agreement on the designated cells -/

/-- The low clause depends only on the values at the owner, the lost top and the designated
cells. -/
theorem AdmitsLowAt.congr (hs : r.AdmitsLowAt s b) (ho : s' r.owner = s r.owner)
    (hl : s' r.lost = s r.lost) (hLo : ∀ d ∈ r.Lo, s' d = s d)
    (hT : ∀ y ∈ r.Tops, s' y = s y) : r.AdmitsLowAt s' b := by
  have hlow : r.lowMax s' = r.lowMax s := Finset.sup_congr rfl hLo
  have hfr : r.frontier s' = r.frontier s := by simp only [frontier, ho, hl]
  intro hlt y hy
  rw [hlow] at hlt
  rw [hfr, hT y hy]
  exact hs hlt y hy

/-! ### The code of a profile -/

section Code

open ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : SourceGapRequests (Fin I.amalgam.card)}
  {P : Prof I}

/-- **The code keeps the low clause**: if the owner, the lost top and the designated cells have
grade at most `k` and `K ≤ k`, the code `orbitCode k (hat I k P)` satisfies the clause at the orbit
map of the field. -/
theorem AdmitsLowAt.code (hs : r.AdmitsLowAt P b) {k : ℕ} (hK : r.K ≤ k)
    (hgr : ∀ d, (d = r.owner ∨ d = r.lost ∨ d ∈ r.Lo ∨ d ∈ r.Tops) →
      I.amalgam.toCellScheme.grade d ≤ k) :
    r.AdmitsLowAt (ProfileTower.code (I := I) k P) (orbitMap k (hat I k P) b) := by
  have hhat (d) (hd : d = r.owner ∨ d = r.lost ∨ d ∈ r.Lo ∨ d ∈ r.Tops) : hat I k P d = P d := by
    rw [hat, CellScheme.splice_of_le (hgr d hd)]
  have h' : r.AdmitsLowAt (hat I k P) b :=
    hs.congr (hhat _ (.inl rfl)) (hhat _ (.inr (.inl rfl)))
      (fun d hd ↦ hhat d (.inr (.inr (.inl hd)))) fun d hd ↦ hhat d (.inr (.inr (.inr hd)))
  exact h'.comp (isWitness_orbitMap k _) hK

/-- **The code keeps the partner form**, when moreover the partner has grade at most `k`. -/
theorem AdmitsLowVia.code {π : Fin I.amalgam.card} (hs : r.AdmitsLowVia π P) {k : ℕ}
    (hK : r.K ≤ k)
    (hgr : ∀ d, (d = r.owner ∨ d = r.lost ∨ d ∈ r.Lo ∨ d ∈ r.Tops) →
      I.amalgam.toCellScheme.grade d ≤ k)
    (hπ : I.amalgam.toCellScheme.grade π ≤ k) :
    r.AdmitsLowVia π (ProfileTower.code (I := I) k P) := by
  have h := AdmitsLowAt.code hs hK hgr
  unfold AdmitsLowVia
  change r.AdmitsLowAt _ (orbitMap k (hat I k P) (hat I k P π))
  rwa [hat, CellScheme.splice_of_le hπ]

end Code

/-! ### The field at the partner -/

/-- **The field is read at the partner**: if `s'` is the image of `s` under a witness `(g, σ)` over
the grades `grade`, and the partner `π` has grade at most that of a cell `ς` with `s' π < s' ς`,
then `σ (s π) = s' π`. -/
theorem apply_eq_of_lt {grade : ι → ℕ} {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) (heq : ∀ d, s' d = min (σ (s d)) (g (grade d))) {π ς : ι}
    (hπς : grade π ≤ grade ς) (hlt : s' π < s' ς) : σ (s π) = s' π := by
  have hgς : s' ς ≤ g (grade ς) := (heq ς).trans_le (min_le_right _ _)
  have hg : s' π < g (grade π) := (hlt.trans_le hgς).trans_le (hw.antitone hπς)
  have h1 := heq π
  rcases le_total (σ (s π)) (g (grade π)) with h2 | h2
  · rw [min_eq_left h2] at h1
    exact h1.symm
  · rw [min_eq_right h2] at h1
    exact absurd h1 hg.ne

end SourceGapRequests

end VaughtConjecture

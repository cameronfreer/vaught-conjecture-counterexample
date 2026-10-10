/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateInstance
import VaughtConjecture.Continuation.LowStateLift

/-!
# The rigid reading refutes the state step on the normalized catalogue

Roadmap, Layer 3 ((R2), the state tower of the LOW construction; the state step of the tower,
`ProfileTower.SLvl.SCatStep`).

**Scope.**  A conditional obstruction to the state tower of
`VaughtConjecture.Continuation.LowStateTower` (whose code splices the fields above each layer and
whose LOW clause reads the proper donor fields of grade at most `K`), stated under the hypotheses
named in each theorem.  It is not on the proof of LOW displays: `StageType.hasLowDisplays_of_padded`
goes through the padded tower (`VaughtConjecture.Continuation.LowPaddedTower`), whose clause over
the proper donor fields of every grade excludes the configuration
(`ProfileTower.not_donorMax_lt_of_subset_coatD`).

The state tower asks the state step only at the **normalized** states (`ProfileTower.sCat`: fixed
by the orbit code over all fields), and it asks the LOW clause of the **orbit code** of the new
state, not of the new state itself.  Both are reached by the rigid reading of
`ProfileTower.not_stateCatStep_of_rigid`.

* **The orbit code is strict on the values** (`Label.orbitCode_lt_orbitCode`): the orbit decoder at
  the least grid point reads the orbit code back literally (`Label.orbitDecoder_orbitCode` with
  `Label.min_orbitCode_gridPoint_zero`) and is monotone.  So the LOW clause of the orbit code of a
  state is active exactly when that of the state is (`Label.donorMax_orbitCode_lt`), and its
  conclusion at a donor top is read back on the values of the state.
* **The cap moved to the top** (`Label.topAbove`): `x ↦ θ x` at or below a cap `h` self-visible at
  `j`, `⊤` above it, is a witness bounded by `j` whenever `θ` is (`Label.isWitness_topAbove`):
  visibility replacement at a threshold `k ≤ j` keeps a label on its side of `h`.
* **The negative on the normalized catalogue** (`ProfileTower.not_sCatStep_of_rigid`): at a
  normalized state with the rigid reading, active below the cap, with a prescription above
  `θ = visibilityReplace j j (P d)` at the cell `u` and at the owner and the lost top, the state
  step of the tower fails.
* **Normalization keeps the configuration** (`ProfileTower.not_sCatStep_of_rigid_state`): from any
  state with the rigid configuration whose cap `h` is a value of the state, its orbit code over all
  fields, the cap `θ_P h` and the prescription `topAbove θ_P h ∘ a` have the configuration at a
  normalized state, so the state step of the tower fails there.

So the state-tower design fails at every legal family realizing the rigid reading with a LOW state
whose cap is one of its values (the shape of the instance: `P t = h`, `P d = μ + i`, `h = μ + j`).
Whether a legal family realizes it is not compiled here.

**What excludes the configuration** (`ProfileTower.not_active_of_mem_fields`).  The activity of
the state uses the donor maximum over the proper donor fields `Nf`; with `Nf = lowN K` (grades at
most `K`) the cells of graded index `(univ.erase y, j)`, `j > K`, do not count.  If `Nf` contains
them (as the maximum over all proper donor cells, `ProfileTower.lowNAll`, does), availability puts
one above the prescribed cell `u`, so above the cap, and the state is not active below the cap: the
rigid reading is never asked to be raised past.

## References

The LOW construction is that of [AFK26]; the rows and their locality are [Kni26, Definition
2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### The orbit code on the values -/

namespace Label

variable {ι : Type*} [Fintype ι] {w : ι → Label.{u}} {k : ℕ}

/-- **The orbit code is strict on the values**: the orbit decoder at the least grid point reads
the orbit code back literally and is monotone. -/
theorem orbitCode_lt_orbitCode {d e : ι} (h : w d < w e) : orbitCode k w d < orbitCode k w e := by
  refine lt_of_not_ge fun hle ↦ ?_
  have hD := (isWitness_orbitDecoder (w := w) (isSelfVisible_gridPoint k 0)
    (gridPoint_ne_bot k 0)).monotone hle
  rw [orbitDecoder_orbitCode (fun _ ↦ min_orbitCode_gridPoint_zero _),
    orbitDecoder_orbitCode (fun _ ↦ min_orbitCode_gridPoint_zero _)] at hD
  exact absurd hD (not_le.mpr h)

/-- The orbit code reflects the order of the values. -/
theorem le_of_orbitCode_le {d e : ι} (h : orbitCode k w d ≤ orbitCode k w e) : w d ≤ w e :=
  not_lt.mp fun hlt ↦ (orbitCode_lt_orbitCode hlt).not_ge h

/-- **The LOW clause of the orbit code is active when that of the labelling is**: the donor
maximum and the cutoff keep their strict order. -/
theorem donorMax_orbitCode_lt {N : Finset ι} {β : ι} (h : donorMax N w < w β) :
    donorMax N (orbitCode k w) < orbitCode k w β := by
  rcases N.eq_empty_or_nonempty with rfl | hne
  · change (∅ : Finset ι).sup _ < _
    rw [Finset.sup_empty, bot_lt_iff_ne_bot, Ne, orbitCode_eq_bot_iff]
    exact ne_bot_of_gt h
  · obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_eq_sup N hne w
    have hle : donorMax N (orbitCode k w) ≤ orbitCode k w f :=
      Finset.sup_le fun f' hf' ↦ monotone_orbitMap k w (hfe ▸ le_sup hf')
    exact hle.trans_lt (orbitCode_lt_orbitCode (by change N.sup w < w β at h; rwa [hfe] at h))

/-! ### The cap moved to the top -/

open Classical in
/-- **The cap moved to the top**: `θ` at or below `h`, the formal top above it. -/
noncomputable def topAbove (θ : Label.{u} → Label.{u}) (h x : Label.{u}) : Label.{u} :=
  if x ≤ h then θ x else ⊤

theorem topAbove_of_le {θ : Label.{u} → Label.{u}} {h x : Label.{u}} (hx : x ≤ h) :
    topAbove θ h x = θ x := ite_eq_left hx

theorem topAbove_of_lt {θ : Label.{u} → Label.{u}} {h x : Label.{u}} (hx : h < x) :
    topAbove θ h x = ⊤ := ite_eq_right (not_le.mpr hx)

/-- **The cap moved to the top is a witness** bounded by `j`, for a witness `θ` bounded by `j`
reflecting `⊥` and a cap `h` self-visible at `j`. -/
theorem isWitness_topAbove {j : ℕ} {θ : Label.{u} → Label.{u}}
    (hθ : IsWitness (stepSuppressor j) θ) (hθb : ∀ x, θ x = ⊥ → x = ⊥) {h : Label.{u}}
    (hh : IsSelfVisible j h) : IsWitness (stepSuppressor j) (topAbove θ h) where
  antitone := hθ.antitone
  isSelfVisible := hθ.isSelfVisible
  map_bot := by rw [topAbove_of_le bot_le, hθ.map_bot]
  monotone x y hxy := by
    by_cases hy : y ≤ h
    · rw [topAbove_of_le (hxy.trans hy), topAbove_of_le hy]; exact hθ.monotone hxy
    · rw [topAbove_of_lt (not_le.mp hy)]; exact le_top
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ j
    · have hhk : IsSelfVisible k h := hh.mono hk
      by_cases hxh : x ≤ h
      · have hv : visibilityReplace k i x ≤ h :=
          (monotone_visibilityReplace hi hxh).trans_eq (hhk.visibilityReplace_eq i)
        rw [topAbove_of_le hxh, topAbove_of_le hv,
          hθ.visibilityReplace_comm x k (by rw [stepSuppressor_of_le hk]; exact le_top) i hi]
      · have hv : h < visibilityReplace k i x :=
          lt_visibilityReplace_of_lt hi hhk (not_le.mp hxh)
        rw [topAbove_of_lt (not_le.mp hxh), topAbove_of_lt hv, visibilityReplace_top]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hx0 : x = ⊥ := by
        by_cases hxh : x ≤ h
        · rw [topAbove_of_le hxh] at hx; exact hθb x hx
        · rw [topAbove_of_lt (not_le.mp hxh)] at hx; exact absurd hx top_ne_bot
      rw [hx0, visibilityReplace_bot, topAbove_of_le bot_le, hθ.map_bot, visibilityReplace_bot]

end Label

/-! ### The negative on the normalized catalogue -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g K : ℕ}
  {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

local notation "𝒜" => lowPred K Nf T o r

local notation "𝒮" => sCat I (g + 1) (lowPred K Nf T o r)

/-- **The rigid reading refutes the state step of the tower.**  As
`ProfileTower.not_stateCatStep_of_rigid`, at a normalized state `P` of the state catalogue
(`ProfileTower.sCat`) over a good state level, with the prescription above
`θ = visibilityReplace (g + 1) (g + 1) (P d)` at the cell `u`, the owner and the lost top: the
orbit code of the new state reads the clause back on the values of the new state
(`Label.orbitCode_lt_orbitCode`), where the donor top stays at most `θ` by rigidity while the owner
and the lost top lie above it. -/
theorem not_sCatStep_of_rigid {N : SLvl I g} (hN : N.Good 𝒜) {x y : Fin (m + 2)}
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + 1) (g + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    {P : CProf I} (hP : P ∈ 𝒮) {h : Label.{u}} (hh : IsSelfVisible (g + 1) h)
    (hsh : IsShort (g + 1) h) (hb : ⊥ < h)
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) < a u)
    (hao : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) < a o)
    (har : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) < a r) :
    ¬ N.SCatStep 𝒜 x := by
  classical
  intro hstep
  set θr := visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) with hθr
  -- the prescription on the state layer
  set w : Fin (N.sS 𝒮).card → Label.{u} :=
    Function.extend (fun e ↦ Fin.castAdd (𝒮).card (N.embed e)) a (fun _ ↦ ⊥) with hw_def
  have hinj : Function.Injective (fun e ↦ Fin.castAdd (𝒮).card (N.embed e)) :=
    fun e e' h ↦ N.embed.injective (Fin.castAdd_injective _ _ h)
  have hwa (e : Fin I.amalgam.card) : w (Fin.castAdd _ (N.embed e)) = a e :=
    hinj.extend_apply _ _ e
  have hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ (univ.erase x, g + 1) :=
    fun h' ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h'.1)
  have hwl : (N.sS 𝒮).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (v := w) hX).mpr
      ((SLvl.Good.isLawfulBelow_old_iff hN (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
        (w := fun e ↦ w (Fin.castAdd _ e))).mpr ?_)
    convert ha using 2 with e
    exact hwa e
  obtain ⟨W, β, hW, hWa, hWP, hA⟩ := hstep P hP h hh hsh hb w hwl
    (fun e hge hse ↦ by rw [hwa]; exact haP e ⟨hse, hge⟩)
  set V : CProf I := withCut W β with hV
  have hlit (e : Fin I.amalgam.card) (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      W e = a e := (hWa e he.2 he.1).trans (hwa e)
  -- `W` reads `d` as `P` does
  have hWd : W d = P (Sum.inl d) := by
    have h1 := hWP (Sum.inl d)
    change min (W d) h = _ at h1
    rw [min_eq_left hd.le] at h1
    rcases le_total (W d) h with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1; exact absurd h1.symm hd.ne
  -- availability below the other coatom and rigidity
  obtain ⟨-, hPC, -, -⟩ := mem_sCat.mp hP
  have hWy : I.amalgam.rows.IsLawfulBelow (univ.erase y, g + 1) (fun e ↦ W e) :=
    hW.isLawfulBelow_erase hy
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWy
  have hw₀b : w₀ ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hw₀]
  obtain ⟨v, hv, huv⟩ := havail u w₀ hw₀b
    (by rw [show I.amalgam.toCellScheme.scope w₀ = univ.erase y from congrArg Prod.fst hw₀]
        exact huy)
    (by rw [hug, show I.amalgam.toCellScheme.grade w₀ = g + 1 from congrArg Prod.snd hw₀])
  have hvg : I.amalgam.toCellScheme.grade v = g + 1 := congrArg Prod.snd (hv.trans hw₀)
  have hvb : v ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hv, hw₀]
  obtain ⟨htv, hdv, hrow⟩ := hrigid v (hv.trans hw₀)
  have hθv : θr < W v := hau.trans_le ((hlit u hux) ▸ huv)
  have hdθ : P (Sum.inl d) ≤ θr := le_visibilityReplace (by omega) _
  have hrig := Scheme.min_le_visibilityReplace_of_rowAt_eq hWy hvb htv hdv
    (by rw [hvg]; exact hrow) (by rw [hWd]; exact hdθ.trans_lt hθv)
  rw [hvg, hWd] at hrig
  have hWt : W t ≤ θr := by
    rcases le_total (W t) (W v) with hle | hle
    · rwa [min_eq_left hle] at hrig
    · rw [min_eq_right hle] at hrig; exact absurd hrig (not_le.mpr hθv)
  -- the clause of the new state is active
  have hdm : donorMax Nf V = donorMax Nf P := by
    refine Finset.sup_congr rfl fun f hf ↦ ?_
    obtain ⟨e, rfl, he⟩ := hNf f hf
    change W e = P (Sum.inl e)
    have h1 := hWP (Sum.inl e)
    change min (W e) h = _ at h1
    rw [min_eq_left he.le] at h1
    rcases le_total (W e) h with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1; exact absurd h1.symm he.ne
  have hβ : min β h = min (P (Sum.inr ())) h := hWP (Sum.inr ())
  have hactV : donorMax Nf V < V (Sum.inr ()) := by
    rw [hdm]
    change donorMax Nf P < β
    exact hact.trans_le (by rw [← hβ]; exact min_le_left _ _)
  -- the clause of the orbit code, read back on the values
  have hlow := hA (donorMax_orbitCode_lt hactV) _ ht
  have hfr := (le_max_right _ _).trans hlow
  unfold Label.frontier at hfr
  have hfr' : min (orbitCode (g + 1) V (Sum.inl o)) (orbitCode (g + 1) V (Sum.inl r)) ≤
      orbitCode (g + 1) V (Sum.inl t) :=
    (min_le_min_left _ (le_visibilityReplace (by omega) _)).trans hfr
  rcases min_le_iff.mp hfr' with h1 | h1
  · have h2 : V (Sum.inl o) ≤ V (Sum.inl t) := le_of_orbitCode_le h1
    change W o ≤ W t at h2
    exact absurd ((hao.trans_le ((hlit o ho).symm ▸ h2)).trans_le hWt) (lt_irrefl _)
  · have h2 : V (Sum.inl r) ≤ V (Sum.inl t) := le_of_orbitCode_le h1
    change W r ≤ W t at h2
    exact absurd ((har.trans_le ((hlit r hr).symm ▸ h2)).trans_le hWt) (lt_irrefl _)

/-- **Normalization keeps the rigid configuration, so the state step of the tower fails**: at any
state `P` (lawful on the cut, LOW at `K ≤ g + 1`) with the rigid reading, active below a cap `h`
self-visible at `g + 1` that is one of its values, with `P d < h` and a prescription `a` above `h`
at the cell `u`, the owner and the lost top: its orbit code over all fields
(`ProfileTower.sCat`), the cap `θ_P h` and the prescription `topAbove θ_P h ∘ a`
(`Label.isWitness_topAbove`) satisfy the hypotheses of `ProfileTower.not_sCatStep_of_rigid`, the
orbit code being strict on the values of `P` (`Label.orbitCode_lt_orbitCode`). -/
theorem not_sCatStep_of_rigid_state {N : SLvl I g} (hN : N.Good 𝒜) (hK : K ≤ g + 1)
    {x y : Fin (m + 2)} (hy : y ∈ (Pts : Finset (Fin (m + 2)))) {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + 1) (g + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    {P : CProf I} (hPC : IsCutLawful I (g + 1) (camal P)) (hPA : 𝒜 P) {h : Label.{u}}
    (hh : IsSelfVisible (g + 1) h) {f₀ : Fin I.amalgam.card ⊕ Unit} (hf₀ : P f₀ = h)
    (hb : ⊥ < h) (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : h < a u) (hao : h < a o) (har : h < a r) :
    ¬ N.SCatStep 𝒜 x := by
  classical
  set θ := orbitMap (g + 1) P with hθdef
  have hθw : IsWitness (stepSuppressor (g + 1)) θ := isWitness_orbitMap (g + 1) P
  have hθb : ∀ z, θ z = ⊥ → z = ⊥ := fun _ ↦ orbitMap_eq_bot_iff.mp
  have hP'f (f : Fin I.amalgam.card ⊕ Unit) : orbitCode (g + 1) P f = θ (P f) := rfl
  set h' := θ h with hh'
  have hh'f : orbitCode (g + 1) P f₀ = h' := by rw [hP'f, hf₀]
  -- the normalized state
  have hB : 2 * Fintype.card (Fin I.amalgam.card ⊕ Unit) ≤ bound I := by
    rw [card_fields]; simp only [bound]; omega
  have hP' : orbitCode (g + 1) P ∈ 𝒮 := by
    refine mem_sCat.mpr ⟨fun f ↦ orbitMap_mem_codeGrid hB _, ⟨?_, ?_⟩, orbitCode_orbitCode,
      hPA.map hθw (stepSuppressor_of_le hK)⟩
    · exact hPC.1.map_of_apply_eq_bot (fun d ↦ d.2.2) hθw fun _ ↦ hθb _
    · exact hPC.2.map_of_apply_eq_bot (fun d ↦ d.2.2) hθw fun _ ↦ hθb _
  -- the new cap
  have hhv' : IsSelfVisible (g + 1) h' :=
    hθw.isSelfVisible_apply hh (by rw [stepSuppressor_of_le le_rfl]; exact le_top)
  have hb' : ⊥ < h' := bot_lt_iff_ne_bot.mpr fun h0 ↦ hb.ne' (hθb _ h0)
  have hlt (e : Fin I.amalgam.card) (he : P (Sum.inl e) < h) :
      orbitCode (g + 1) P (Sum.inl e) < h' := by
    rw [← hh'f]; exact orbitCode_lt_orbitCode (by rw [hf₀]; exact he)
  have hact' : donorMax Nf (orbitCode (g + 1) P) < min (orbitCode (g + 1) P (Sum.inr ())) h' := by
    refine lt_min (donorMax_orbitCode_lt (lt_min_iff.mp hact).1) ?_
    rw [← hh'f]
    exact donorMax_orbitCode_lt (by rw [hf₀]; exact (lt_min_iff.mp hact).2)
  -- the new prescription
  set a' : Prof I := fun e ↦ topAbove θ h (a e) with ha'def
  have hψ := isWitness_topAbove hθw hθb hh
  have ha' : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a' e) :=
    ha.map_of_apply_eq_bot (fun d ↦ d.2.2) hψ fun e h0 ↦ by
      by_cases hle : a e ≤ h
      · rw [topAbove_of_le hle] at h0; exact hθb _ h0
      · rw [topAbove_of_lt (not_le.mp hle)] at h0; exact absurd h0 top_ne_bot
  have haP' (e : Fin I.amalgam.card)
      (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      min (a' e) h' = min (orbitCode (g + 1) P (Sum.inl e)) h' := by
    have h1 := haP e he
    rcases lt_or_ge (a e) h with hlt' | hge
    · have hPe : P (Sum.inl e) = a e := by
        rw [min_eq_left hlt'.le] at h1
        rcases le_total (P (Sum.inl e)) h with hle | hle
        · rw [min_eq_left hle] at h1; exact h1.symm
        · rw [min_eq_right hle] at h1; exact absurd h1 hlt'.ne
      change min (topAbove θ h (a e)) h' = min (θ (P (Sum.inl e))) h'
      rw [topAbove_of_le hlt'.le, hPe]
    · have hPe : h ≤ P (Sum.inl e) := by
        rw [min_eq_right hge] at h1
        exact min_eq_right_iff.mp h1.symm
      have hA : h' ≤ a' e := by
        change θ h ≤ topAbove θ h (a e)
        rcases hge.lt_or_eq with hgt | heq
        · rw [topAbove_of_lt hgt]; exact le_top
        · rw [← heq, topAbove_of_le le_rfl]
      rw [min_eq_right hA]
      exact (min_eq_right (monotone_orbitMap (g + 1) P hPe)).symm
  have htop (z : Fin I.amalgam.card) (hz : h < a z) :
      visibilityReplace (g + 1) (g + 1) (orbitCode (g + 1) P (Sum.inl d)) < a' z := by
    change _ < topAbove θ h (a z)
    rw [topAbove_of_lt hz, lt_top_iff_ne_top, Ne, visibilityReplace_eq_top_iff]
    exact orbitCode_ne_top _
  exact not_sCatStep_of_rigid hN hy hw₀ hrigid ht hux huy hug ho hr hP' hhv' (isShort_orbitMap _)
    hb' (fun f hf ↦ by obtain ⟨e, rfl, he⟩ := hNf f hf; exact ⟨e, rfl, hlt e he⟩) hact'
    (hlt d hd) ha' haP' (htop u hau) (htop o hao) (htop r har)

/-- **The all-grades donor maximum excludes the rigid configuration**: if the proper donor fields
`Nf` contain every cell of graded index `(univ.erase y, j)` (as for the donor maximum over all
proper donor cells, `ProfileTower.lowNAll`, and not for `ProfileTower.lowN K` at `K < j`), a state
lawful on the cut agreeing with a prescription above the cap at the cell `u` cannot be active below
the cap: availability puts a cell of graded index `(univ.erase y, j)`, a proper donor field, above
`u`, hence at least the cap. -/
theorem not_active_of_mem_fields {j : ℕ} {x y : Fin (m + 2)}
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) {u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, j))
    (hNw : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, j) → Sum.inl w ∈ Nf)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y) (hug : I.amalgam.toCellScheme.grade u = j)
    {P : CProf I} (hPC : IsCutLawful I j (camal P)) {h : Label.{u}} {a : Prof I}
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a e) h = min (P (Sum.inl e)) h) (hau : h < a u) :
    ¬ donorMax Nf P < min (P (Sum.inr ())) h := by
  intro hact
  have hPu : h ≤ P (Sum.inl u) := by
    have h1 := haP u hux
    rw [min_eq_right hau.le] at h1
    exact min_eq_right_iff.mp h1.symm
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp (hPC.isLawfulBelow_erase hy)
  have hw₀b : w₀ ∈ I.amalgam.toCellScheme.below (univ.erase y, j) := by
    rw [CellScheme.mem_below, hw₀]
  obtain ⟨v, hv, huv⟩ := havail u w₀ hw₀b
    (by rw [show I.amalgam.toCellScheme.scope w₀ = univ.erase y from congrArg Prod.fst hw₀]
        exact huy)
    (by rw [hug, show I.amalgam.toCellScheme.grade w₀ = j from congrArg Prod.snd hw₀])
  have hv' : h ≤ donorMax Nf P :=
    (hPu.trans huv).trans (le_donorMax (hNw v (hv.trans hw₀)))
  exact absurd (hv'.trans_lt (hact.trans_le (min_le_right _ _))) (lt_irrefl _)

end ProfileTower

end VaughtConjecture

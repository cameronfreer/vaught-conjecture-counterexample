/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateLevel

/-!
# The state tower above the controllers

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the levels above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

Over a good level `L` at the grade `g` (the levels below the controllers, indexed by amalgam
profiles), **the state tower** (`ProfileTower.sTower`) is `L` read as a state level, then the next
state levels on the state catalogues of a predicate `A` at the grades `g + 1, g + 2, …`.  The layer
at `K = g + 1` is the layer of controllers; every layer above has one cell per state.

**Good and extending at `⊥`** (`ProfileTower.sTower_good`,
`ProfileTower.SLvl.Good.hasBotExtension_next`, compiled in this repository).  Up to the grade `m`,
the state tower is good when `A` holds with the cutoff `⊥` and is kept by the state codes from
`K` on, given the lift of every layer from the two coatoms (`ProfileTower.STowerLifts`, the
hypothesis: for the LOW clause, the LOW step at every grade from `K` to `m`); the forgetful level
of every layer extends at `⊥`.

**The LOW clause is kept by the state codes** (`ProfileTower.lowPred_scode`, compiled in this
repository): the designated fields have grade at most `K`, where the splice keeps them, and the
orbit map is a witness with suppressor `⊤` at `K`.

**Separated states** (`ProfileTower.SepInv`, `ProfileTower.cutoffCut_lt_of_sepInv`, compiled in
this repository).  A state is separated when its owner and donor tops carry its cutoff and its
proper donor values lie in keys strictly below the key of its cutoff at every grade; its cutoff cut
then lies below its cutoff.  The partner of a canonical state whose owner carries its cutoff is
canonical (`ProfileTower.orbitCode_update_cutoffCut`).

The bottom state, the two chain bounds of the state tower and the separation of state codes, which
served the reading of the actual state by the state tower given its lifts, remain on the research
branch `research/port-low-padded`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

/-- **Labels in strictly smaller blocks have strictly smaller keys at every grade**: if `a` and `c`
have the keys `ω * b + j` and `ω * b' + j` at `j` with `b < b'`, then the key of `a` is below that
of `c` at every grade. -/
theorem visibilityReplace_lt_of_block_lt {a c : Label.{u}} {j b b' : ℕ}
    (ha : visibilityReplace j j a = gridPoint j b) (hc : visibilityReplace j j c = gridPoint j b')
    (hbb : b < b') (k : ℕ) : visibilityReplace k k a < visibilityReplace k k c := by
  have hdiv {x : Label.{u}} {n : ℕ} (hx : visibilityReplace j j x = gridPoint j n) :
      ∃ o : Ordinal.{u}, x = ((o : WithTop Ordinal.{u}) : Label.{u}) ∧ o / Ordinal.omega0 = n := by
    induction x using recBotCoeTop with
    | bot => rw [visibilityReplace_bot] at hx; exact absurd hx.symm (gridPoint_ne_bot _ _)
    | top => rw [visibilityReplace_top] at hx; exact absurd hx.symm (gridPoint_ne_top _ _)
    | coe o =>
      refine ⟨o, rfl, ?_⟩
      have h1 : Ordinal.visibilityReplace j j o = Ordinal.omega0 * n + j :=
        WithTop.coe_injective (WithBot.coe_injective hx)
      rw [← Ordinal.visibilityReplace_div j j o, h1, Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
        Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 j), add_zero]
  obtain ⟨o, rfl, ho⟩ := hdiv ha
  obtain ⟨o', rfl, ho'⟩ := hdiv hc
  have hlt : Ordinal.visibilityReplace k k o < Ordinal.visibilityReplace k k o' := by
    have h1 := Ordinal.lt_mul_div_add (Ordinal.visibilityReplace k k o) Ordinal.omega0_ne_zero
    have h2 := Ordinal.mul_div_le (Ordinal.visibilityReplace k k o') Ordinal.omega0
    rw [Ordinal.visibilityReplace_div] at h1 h2
    rw [ho] at h1
    rw [ho'] at h2
    refine h1.trans_le (le_trans ?_ h2)
    rw [← mul_add_one]
    have hb1 : ((b : Ordinal.{u}) + 1) ≤ (b' : Ordinal.{u}) := by exact_mod_cast hbb
    gcongr
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hlt)

end VaughtConjecture.Label

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### Extension at `⊥` through a state layer -/

section Bot

variable {g : ℕ} {N : SLvl I g} {A : CProf I → Prop}

local notation "𝒮" => sCat I (g + 1) A

/-- The old cells of a good state level are a source prefix off the ground set. -/
theorem SLvl.Good.isLawfulBelow_old_iff (hN : N.Good A) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {w : Fin N.S.card → Label.{u}} :
    N.S.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (N.embed d)) := by
  have h : I.amalgam.toCellScheme.IsSourcePrefix N.S.toCellScheme N.embed X :=
    ⟨hN.lowerEmb, hN.scope_embed, fun z hz ↦ hN.mem_range z fun he ↦
      hX (univ_subset_iff.mp (he ▸ (hz.1 : N.S.toCellScheme.scope z ⊆ X.1)))⟩
  rw [← h.isLawfulBelow_iff le_rfl, hN.comap_rows]
  rfl

/-- **The forgetful level of the next state level extends at `⊥`**: the decoded row of the state
of the old labels with the cutoff `⊥`. -/
theorem SLvl.Good.hasBotExtension_next (hN : N.Good A) (hA0 : ∀ W : Prof I, A (withCut W ⊥)) :
    (N.next 𝒮).forget.HasBotExtension := by
  classical
  change ∀ w : Fin (N.sS 𝒮).card → Label.{u},
    (N.sS 𝒮).rows.IsLawfulBelow (coatC, g + 1) (fun z ↦ w z) →
    (N.sS 𝒮).rows.IsLawfulBelow (coatD, g + 1) (fun z ↦ w z) →
    ∃ r : (N.sS 𝒮).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (N.sS 𝒮).rows.IsLawfulBelow (univ, g + 1) r ∧
        ∀ z, (N.sS 𝒮).toCellScheme.scope z.1 ≠ univ → r z = w z
  intro w hwC hwD
  set W : Prof I := fun d ↦
    if I.amalgam.toCellScheme.grade d ≤ g + 1 then w (Fin.castAdd _ (N.embed d)) else ⊥ with hW
  have hWc (x : Fin (m + 2))
      (hw : (N.sS 𝒮).rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ w z) :
      I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ W d := by
    have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (v := w)
      (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1))).mp hw
    have h2 := (hN.isLawfulBelow_old_iff (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase x, g + 1))
      fun d hd ↦ (show W d = _ from ite_eq_left hd.2).symm).mp h2
  have hWcut : IsCutLawful I (g + 1) W := ⟨hWc _ hwC, hWc _ hwD⟩
  set Q : CProf I := withCut (code (g + 1) W) ⊥ with hQ
  have hQC : Q ∈ 𝒮 := mem_sCat.mpr ⟨fun f ↦ by
      rcases f with d | z
      exacts [code_mem_codeGrid _ _ _, mem_insert_self _ _],
    (mem_cat.mp (code_mem_cat_of_isCutLawful hWcut)).1,
    by rw [hQ, orbitCode_withCut_bot, orbitCode_orbitCode], hA0 _⟩
  have hQW (d : Fin I.amalgam.card) :
      min (code (g + 1) W d) (gridPoint (g + 1) 0) = min (hat I (g + 1) W d)
        (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) (hat I (g + 1) W) (gridPoint (g + 1) 0) (N.Φs 𝒮 Q z),
    (hN.isLawfulBelow_Φs hQC (mem_sCat.mp hQC).1 (mem_sCat.mp hQC).2.1
      (mem_sCat.mp hQC).2.2.2).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun z hz ↦ ?_⟩
  obtain ⟨z, hzm⟩ := z
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hz
  | left e =>
    have hne : N.S.toCellScheme.scope e ≠ univ := by
      rwa [show (N.sS 𝒮).toCellScheme.scope (Fin.castAdd _ e) = N.S.toCellScheme.scope e from
        Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _] at hz
    obtain ⟨d, rfl⟩ := hN.mem_range e hne
    have hd : I.amalgam.toCellScheme.grade d ≤ g + 1 := by
      have := hzm.2
      rwa [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
        show N.S.toCellScheme.gradedIndex (N.embed d) = I.amalgam.toCellScheme.gradedIndex d from
          Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)] at this
    change orbitDecoder (g + 1) (hat I (g + 1) W) (gridPoint (g + 1) 0)
      (N.Φs 𝒮 Q (Fin.castAdd _ (N.embed d))) = w (Fin.castAdd _ (N.embed d))
    rw [SLvl.Φs_castAdd, hN.literal]
    change orbitDecoder (g + 1) (hat I (g + 1) W) (gridPoint (g + 1) 0)
      (orbitCode (g + 1) (hat I (g + 1) W) d) = _
    rw [orbitDecoder_orbitCode hQW d, hat_of_le hd]
    exact ite_eq_left hd

end Bot

/-! ### The LOW clause is kept by the state codes -/

section Low

variable {K : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The LOW clause is kept by the state code at a grade `j ≥ K`**, when the designated fields
have grade at most `K`. -/
theorem lowPred_scode (hF : FieldsLE K N T o) (hr : I.amalgam.toCellScheme.grade r ≤ K) {j : ℕ}
    (hj : K ≤ j) {P : CProf I} (h : lowPred K N T o r P) : lowPred K N T o r (scode j P) := by
  have hhat : ∀ d, I.amalgam.toCellScheme.grade d ≤ K → hatS j P (Sum.inl d) = P (Sum.inl d) :=
    fun d hd ↦ hat_of_le (hd.trans hj)
  have h1 : lowPred K N T o r (hatS j P) := by
    intro hlt x hx
    have hdm : donorMax N (hatS j P) = donorMax N P := donorMax_congr fun f hf ↦ by
      obtain ⟨d, rfl, hd⟩ := hF.1 f hf
      exact hhat d hd
    have hfr : Label.frontier K (Sum.inl o) (Sum.inl r) (hatS j P) =
        Label.frontier K (Sum.inl o) (Sum.inl r) P := by
      unfold Label.frontier
      rw [hhat o hF.2.2, hhat r hr]
    obtain ⟨d, rfl, hd⟩ := hF.2.1 x hx
    rw [hdm] at hlt
    have := h hlt _ hx
    rw [hfr, hhat d hd]
    exact this
  exact h1.map (isWitness_orbitMap j (hatS j P)) (stepSuppressor_of_le hj)

end Low

/-! ### The state tower -/

section Tower

variable {g : ℕ} (L : Lvl I g) (A : CProf I → Prop)

/-- **The state tower** over a level `L` at the grade `g`: `L` read as a state level, then the next
state levels on the state catalogues of `A`. -/
noncomputable def sTower : (J : ℕ) → SLvl I (g + J)
  | 0 => L.toS
  | J + 1 => (sTower J).next (sCat I (g + J + 1) A)

/-- **The lifts of the state tower** below the layer `J₀`: every layer at a grade `g + J + 1` with
`J < J₀` lifts capped from the two coatoms into the full face at its grade. -/
def STowerLifts (J₀ : ℕ) : Prop :=
  ∀ J < J₀, ∀ x ∈ (Pts : Finset (Fin (m + 2))),
    ((sTower L A J).sS (sCat I (g + J + 1) A)).rows.CappedLift (X := (univ.erase x, g + J + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + J + 1)) ⟨erase_subset _ _, le_rfl⟩

variable {L A}

/-- **The state tower is good up to the grade `m`**, given its lifts, when `A` holds with the
cutoff `⊥` and is kept by the state codes at the grades above `g`. -/
theorem sTower_good (hL : L.Good) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAc : ∀ j, g + 1 ≤ j → ∀ P : CProf I, A P → A (scode j P)) {J₀ : ℕ}
    (hlift : STowerLifts L A J₀) : ∀ J, J ≤ J₀ → g + J ≤ m → (sTower L A J).Good A
  | 0, _, _ => hL.toS A
  | J + 1, hJ, hm => (sTower_good hL hA0 hAc hlift J (by omega) (by omega)).next (by omega) hA0
      (hAc _ (by omega)) (hlift J (by omega))

/-- The agreement height with the partner is at most the lowered cutoff. -/
theorem agreementHeight_update_le {G : Finset Label.{u}} (hG : ⊥ ∈ G) (s : CProf I)
    {c : Label.{u}} (hc : c < s (Sum.inr ())) :
    agreementHeight G s (Function.update s (Sum.inr ()) c) ≤ c := by
  by_contra hgt
  rw [not_le] at hgt
  have h := (agreementHeight_spec hG s (Function.update s (Sum.inr ()) c)).2 (Sum.inr ())
  rw [Function.update_self, min_eq_left hgt.le] at h
  exact (lt_min hc hgt).ne' h

local notation "𝒦" => sCat I (g + 1) A

end Tower

/-! ### The separator of the actual state -/

section Sep

variable {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o : Fin I.amalgam.card}

variable (N T o) in
/-- A state is **separated** when its owner and donor tops carry its cutoff, other than `⊥`, and its
proper donor values other than `⊥` lie in keys strictly below the key of its cutoff at every
grade. -/
def SepInv (P : CProf I) : Prop :=
  P (Sum.inr ()) ≠ ⊥ ∧ P (Sum.inl o) = P (Sum.inr ()) ∧ (∀ x ∈ T, P x = P (Sum.inr ())) ∧
    ∀ f ∈ N, P f ≠ ⊥ → ∀ k, visibilityReplace k k (P f) < visibilityReplace k k (P (Sum.inr ()))

/-- **The cutoff cut of a separated state code lies below its cutoff.** -/
theorem cutoffCut_lt_of_sepInv {K : ℕ} {P : CProf I} (h : SepInv N T o P) :
    cutoffCut K N P < P (Sum.inr ()) := by
  rcases N.eq_empty_or_nonempty with he | hne
  · rw [cutoffCut, donorMax, he, sup_empty, visibilityReplace_bot]
    exact bot_lt_iff_ne_bot.mpr h.1
  obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne P
  rw [cutoffCut, donorMax, hfeq]
  by_cases hf0 : P f = ⊥
  · rw [hf0, visibilityReplace_bot]; exact bot_lt_iff_ne_bot.mpr h.1
  have hlt := h.2.2.2 f hf hf0 K
  by_contra hge
  rw [not_lt] at hge
  have := visibilityReplace_le_of_le le_rfl (isSelfVisible_visibilityReplace_self K (P f)) hge
  exact absurd this (not_le.mpr hlt)

/-- **The partner of a canonical state whose owner carries its cutoff is canonical**: lowering
the cutoff to the cutoff cut keeps the keys (the old cutoff key stays at the owner, the cutoff cut
has the key of the donor maximum) and the orbit keys (the cutoff cut is self-visible), so the orbit
map is unchanged, and it fixes the cutoff cut, a grid point of the code block of its key. -/
theorem orbitCode_update_cutoffCut {k : ℕ} {o' : Fin I.amalgam.card} (hNi : Sum.inr () ∉ N)
    {s : CProf I} (hs : orbitCode k s = s) (ho : s (Sum.inl o') = s (Sum.inr ())) :
    orbitCode k (Function.update s (Sum.inr ()) (cutoffCut k N s)) =
      Function.update s (Sum.inr ()) (cutoffCut k N s) := by
  classical
  set c := cutoffCut k N s with hc
  set s' := Function.update s (Sum.inr ()) c with hs'
  have hval (f : Fin I.amalgam.card ⊕ Unit) (hf : f ≠ Sum.inr ()) : s' f = s f :=
    Function.update_of_ne hf _ _
  have hfix (y : Label.{u}) (hy : ∃ f, s f = y) : orbitMap k s y = y := by
    obtain ⟨f, rfl⟩ := hy
    exact congrFun hs f
  -- the cutoff cut is `⊥` or the key of a value at a proper field
  have hcases : c = ⊥ ∨ ∃ f ∈ N, s f ≠ ⊥ ∧ c = visibilityReplace k k (s f) := by
    rcases N.eq_empty_or_nonempty with he | hne
    · left; rw [hc, cutoffCut, donorMax, he, sup_empty, visibilityReplace_bot]
    obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne s
    by_cases hf0 : s f = ⊥
    · left; rw [hc, cutoffCut, donorMax, hfeq, hf0, visibilityReplace_bot]
    · right; exact ⟨f, hf, hf0, by rw [hc, cutoffCut, donorMax, hfeq]⟩
  have hcsv : IsSelfVisible k c := isSelfVisible_cutoffCut s
  have hinr_ne (f : Fin I.amalgam.card ⊕ Unit) (hf : f ∈ N) : f ≠ Sum.inr () :=
    fun h ↦ hNi (h ▸ hf)
  -- the keys
  have hkeys (y : Label.{u}) (hy : y ≠ ⊥) :
      (∃ f, s f ≠ ⊥ ∧ visibilityReplace k k (s f) = y) ↔
        ∃ f, s' f ≠ ⊥ ∧ visibilityReplace k k (s' f) = y := by
    constructor
    · rintro ⟨f, hf0, hfy⟩
      by_cases hf : f = Sum.inr ()
      · subst hf
        refine ⟨Sum.inl o', ?_, ?_⟩
        · rw [hval _ Sum.inl_ne_inr, ho]; exact hf0
        · rw [hval _ Sum.inl_ne_inr, ho]; exact hfy
      · exact ⟨f, by rw [hval f hf]; exact hf0, by rw [hval f hf]; exact hfy⟩
    · rintro ⟨f, hf0, hfy⟩
      by_cases hf : f = Sum.inr ()
      · subst hf
        rw [hs', Function.update_self] at hf0 hfy
        rcases hcases with h0 | ⟨f', hf', hf'0, hcf⟩
        · exact absurd h0 hf0
        · refine ⟨f', hf'0, ?_⟩
          rw [← hfy, hcf, visibilityReplace_self_visibilityReplace le_rfl]
      · exact ⟨f, by rw [← hval f hf]; exact hf0, by rw [← hval f hf]; exact hfy⟩
  have hkey (x : Label.{u}) : IsKey k s' x ↔ IsKey k s x := by
    by_cases hx : x = ⊥
    · subst hx
      exact ⟨fun h ↦ absurd rfl h.ne_bot, fun h ↦ absurd rfl h.ne_bot⟩
    have hRx : visibilityReplace k k x ≠ ⊥ := by rwa [Ne, visibilityReplace_eq_bot_iff]
    exact (hkeys _ hRx).symm
  have horb (x : Label.{u}) : IsOrbitKey k s' x ↔ IsOrbitKey k s x := by
    constructor
    · rintro ⟨f, hfx, hf⟩
      by_cases hfi : f = Sum.inr ()
      · subst hfi
        rw [hs', Function.update_self] at hf
        exact absurd hcsv hf
      · exact ⟨f, by rw [← hval f hfi]; exact hfx, by rw [← hval f hfi]; exact hf⟩
    · rintro ⟨f, hfx, hf⟩
      by_cases hfi : f = Sum.inr ()
      · subst hfi
        exact ⟨Sum.inl o', by rw [hval _ Sum.inl_ne_inr, ho]; exact hfx,
          by rw [hval _ Sum.inl_ne_inr, ho]; exact hf⟩
      · exact ⟨f, by rw [hval f hfi]; exact hfx, by rw [hval f hfi]; exact hf⟩
  have hrank (x : Label.{u}) : keyRank k s' x = keyRank k s x := by
    unfold keyRank valueRank
    congr 1
    ext y
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨f, rfl⟩, hy, hyx⟩
      have hf0 : s' f ≠ ⊥ := fun h ↦ hy (by rw [h, visibilityReplace_bot])
      obtain ⟨f', -, hf'⟩ := (hkeys _ hy).mpr ⟨f, hf0, rfl⟩
      exact ⟨⟨f', hf'⟩, hy, hyx⟩
    · rintro ⟨⟨f, rfl⟩, hy, hyx⟩
      have hf0 : s f ≠ ⊥ := fun h ↦ hy (by rw [h, visibilityReplace_bot])
      obtain ⟨f', -, hf'⟩ := (hkeys _ hy).mp ⟨f, hf0, rfl⟩
      exact ⟨⟨f', hf'⟩, hy, hyx⟩
  have hmap (x : Label.{u}) : orbitMap k s' x = orbitMap k s x :=
    orbitMap_congr (hrank x) (hkey x) (horb x)
  funext f
  rw [orbitCode_apply, hmap]
  by_cases hfi : f = Sum.inr ()
  · subst hfi
    rw [hs', Function.update_self]
    rcases hcases with h0 | ⟨f', -, hf'0, hcf⟩
    · rw [h0, orbitMap_bot]
    · have hsf : orbitMap k s (s f') = s f' := hfix _ ⟨f', rfl⟩
      have hgp : c = gridPoint k (codeBlock k s (s f')) := by
        rw [hcf, ← hsf, visibilityReplace_orbitMap hf'0, hsf]
      have hc0 : c ≠ ⊥ := by rw [hgp]; exact gridPoint_ne_bot _ _
      have hcb : codeBlock k s c = codeBlock k s (s f') :=
        codeBlock_congr (by rw [hcf, visibilityReplace_self_visibilityReplace le_rfl])
      by_cases hco : IsOrbitKey k s c
      · rw [orbitMap_of_isOrbitKey hco, hcb, ← hgp]
        exact moveToBlock_eq_self (k := k) rfl
      · rw [orbitMap_of_not_isOrbitKey hc0 hco, hcb, ← hgp]
  · rw [hval f hfi]
    exact hfix _ ⟨f, rfl⟩

end Sep

end VaughtConjecture.ProfileTower

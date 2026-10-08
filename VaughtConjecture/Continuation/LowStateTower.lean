/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateLevel

/-!
# The state tower above the controllers and the reading of the actual state

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

**The two chain bounds** (`ProfileTower.le_sTower_hi`, `ProfileTower.sTower_lo_le`, compiled in this
repository).  The **bottom state** of `P` through `J` layers (`ProfileTower.sBot`) is the state code
of the state code … of `P` down to `K + 1`.  At every state `P`, the section of the layer at
`K + J` reads the controller of the state code at `K` of the bottom state at least at the cutoff
of `P` (the controller of a state reads itself at the ceiling of the grid, decoded above the code of
the cutoff; each decoder above reads the code of the cutoff back as the cutoff), and the controller
of its partner over all proper donor cells at most at the cutoff cut of the donor maximum of `P`
(the agreement height with the partner is at most the cutoff cut, and every decoder commutes with
the visibility replacement at `K` and reads codes back).

**The separator of the actual state** (`ProfileTower.SepInv`, `ProfileTower.sepInv_scode`, compiled
in this repository).  A state whose owner and donor tops carry its cutoff, and whose proper donor
values lie in keys strictly below the key of its cutoff at every grade, keeps both properties under
the state code: equal values have equal codes, and keys strictly apart have code blocks strictly
apart (`Label.codeBlock_lt_codeBlock`), hence keys strictly apart at every grade
(`Label.visibilityReplace_lt_of_block_lt`).  The actual state (the glued labels with the cutoff `⊤`)
is such a state; so its bottom code `s` has its cutoff cut in the grid and below its cutoff, and `s`
and its partner are LOW states of the catalogue at `K`.

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
    (mem_cat.mp (code_mem_cat_of_isCutLawful hWcut)).1, hA0 _⟩
  have hQW (d : Fin I.amalgam.card) :
      min (code (g + 1) W d) (gridPoint (g + 1) 0) = min (hat I (g + 1) W d)
        (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) (hat I (g + 1) W) (gridPoint (g + 1) 0) (N.Φs 𝒮 Q z),
    (hN.isLawfulBelow_Φs hQC (mem_sCat.mp hQC).1 (mem_sCat.mp hQC).2.1
      (mem_sCat.mp hQC).2.2).map_of_apply_eq_bot (fun z ↦ z.2.2)
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

/-- The cells of the layer of controllers among those of the layers above. -/
noncomputable def sEmb : (J : ℕ) → Fin (sTower L A 1).S.card → Fin (sTower L A (J + 1)).S.card
  | 0 => id
  | J + 1 => Fin.castAdd _ ∘ sEmb J

/-- **The layer of controllers is a grade prefix of every layer above**, at `K = g + 1`. -/
theorem isGradePrefix_sEmb :
    ∀ J, Scheme.IsGradePrefix (sTower L A 1).S (sTower L A (J + 1)).S (sEmb (L := L) (A := A) J)
      (g + 1)
  | 0 => Scheme.IsGradePrefix.id _ _
  | J + 1 => (Scheme.IsGradePrefix.castAdd (S := (sTower L A (J + 1)).S) (k := g + (J + 1) + 1)
      (M := (sCat I (g + (J + 1) + 1) A).card)
      (r := fun i ↦ (sTower L A (J + 1)).Φs (sCat I (g + (J + 1) + 1) A)
        ((sCat I (g + (J + 1) + 1) A).equivFin.symm i).1)
      (h := (sTower L A (J + 1)).not_le) (by omega)).comp (isGradePrefix_sEmb J)

/-- The **bottom state** of `P` through `J` layers: the state code at `g + J + 1`, …, `g + 2`. -/
noncomputable def sBot (g : ℕ) : (J : ℕ) → CProf I → CProf I
  | 0 => id
  | J + 1 => fun P ↦ sBot g J (scode (g + J + 2) P)

/-- The splice of a state is at most the state. -/
theorem hatS_le (k : ℕ) (P : CProf I) (f : Fin I.amalgam.card ⊕ Unit) : hatS k P f ≤ P f := by
  rcases f with d | z
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
    · exact (hat_of_le hd).le
    · exact (hat_of_lt (_root_.not_le.mp hd)).le.trans bot_le
  · exact le_rfl

/-- **A decoder reads the cutoff cut of the donor maximum of a state code at most at the cutoff
cut of the donor maximum of the state**, at the grades `k ≥ K`. -/
theorem upperDecoder_cutoff_le {K k : ℕ} (hK : K ≤ k) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (P : CProf I) :
    upperDecoderAt k (k + 1) (bound I) (hatS k P)
      (visibilityReplace K K (donorMax N (scode k P))) ≤
      visibilityReplace K K (donorMax N P) := by
  have hw := isWitness_upperDecoderAt (k := k) (K := k + 1) (w := hatS k P) (B := bound I)
    (by omega)
  rw [hw.visibilityReplace_comm _ K (by rw [stepSuppressor_of_le hK]; exact le_top) K le_rfl]
  refine monotone_visibilityReplace le_rfl ?_
  rcases N.eq_empty_or_nonempty with he | hne
  · rw [donorMax, he, sup_empty, upperDecoderAt_bot]; exact bot_le
  obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne (scode k P)
  rw [donorMax, hfeq, upperDecoderAt_orbitCode]
  exact (hatS_le k P f).trans (le_donorMax hf)

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

/-- **The first chain bound**: the section of the layer at `g + J + 1` reads the controller of the
state code at `K` of the bottom state of `P` at least at the cutoff of `P`. -/
theorem le_sTower_hi : ∀ (J : ℕ) (P : CProf I) (i : Fin (𝒦).card),
    ((𝒦).equivFin.symm i).1 = scode (g + 1) (sBot g J P) →
    P (Sum.inr ()) ≤ (sTower L A (J + 1)).σs P (sEmb J (Fin.natAdd L.S.card i))
  | 0, P, i, hi => by
    change P (Sum.inr ()) ≤ L.toS.nextσ 𝒦 P (Fin.natAdd _ i)
    rw [SLvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]), SLvl.Φs_natAdd, hi]
    change P (Sum.inr ()) ≤ upperDecoderAt (g + 1) (g + 2) (bound I) (hatS (g + 1) P)
      (agreementHeight (grid (g + 1) (bound I)) (scode (g + 1) P) (scode (g + 1) P))
    rw [agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
    have h := upperDecoderAt_orbitCode (k := g + 1) (K := g + 2) (B := bound I)
      (w := hatS (g + 1) P) (Sum.inr ())
    refine le_of_eq_of_le h.symm ((isWitness_upperDecoderAt (by omega)).monotone ?_)
    exact le_gridPoint_of_mem_codeGrid (scode_mem_codeGrid _ _ _)
  | J + 1, P, i, hi => by
    have ih := le_sTower_hi J (scode (g + J + 2) P) i hi
    have hgr : (sTower L A (J + 1)).S.toCellScheme.grade (sEmb J (Fin.natAdd L.S.card i)) =
        g + 1 :=
      ((isGradePrefix_sEmb J).lowerEmb.grade_eq _).trans
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    change P (Sum.inr ()) ≤ (sTower L A (J + 1)).nextσ (sCat I (g + (J + 1) + 1) A) P
      (Fin.castAdd _ (sEmb J (Fin.natAdd L.S.card i)))
    rw [SLvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd, hgr]; omega),
      SLvl.Φs_castAdd]
    have h := upperDecoderAt_orbitCode (k := g + J + 2) (K := g + J + 2 + 1) (B := bound I)
      (w := hatS (g + J + 2) P) (Sum.inr ())
    exact le_of_eq_of_le h.symm ((isWitness_upperDecoderAt (by omega)).monotone ih)

/-- **The second chain bound**: the section of the layer at `g + J + 1` reads the controller of the
partner, over a set `N` of fields, of the state code at `K` of the bottom state of `P` at most at
the cutoff cut over `N` of `P`, when that partner lowers the cutoff. -/
theorem sTower_lo_le (N : Finset (Fin I.amalgam.card ⊕ Unit)) :
    ∀ (J : ℕ) (P : CProf I) (i : Fin (𝒦).card),
    ((𝒦).equivFin.symm i).1 = Function.update (scode (g + 1) (sBot g J P)) (Sum.inr ())
      (cutoffCut (g + 1) N (scode (g + 1) (sBot g J P))) →
    cutoffCut (g + 1) N (scode (g + 1) (sBot g J P)) <
      scode (g + 1) (sBot g J P) (Sum.inr ()) →
    (sTower L A (J + 1)).σs P (sEmb J (Fin.natAdd L.S.card i)) ≤ cutoffCut (g + 1) N P
  | 0, P, i, hi, hlt => by
    change L.toS.nextσ 𝒦 P (Fin.natAdd _ i) ≤ _
    rw [SLvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]), SLvl.Φs_natAdd, hi]
    refine ((isWitness_upperDecoderAt (by omega)).monotone
      (agreementHeight_update_le (bot_mem_grid _ _) _ hlt)).trans ?_
    exact upperDecoder_cutoff_le le_rfl N P
  | J + 1, P, i, hi, hlt => by
    have ih := sTower_lo_le N J (scode (g + J + 2) P) i hi hlt
    have hgr : (sTower L A (J + 1)).S.toCellScheme.grade (sEmb J (Fin.natAdd L.S.card i)) =
        g + 1 :=
      ((isGradePrefix_sEmb J).lowerEmb.grade_eq _).trans
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    change (sTower L A (J + 1)).nextσ (sCat I (g + (J + 1) + 1) A) P
      (Fin.castAdd _ (sEmb J (Fin.natAdd L.S.card i))) ≤ _
    rw [SLvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd, hgr]; omega),
      SLvl.Φs_castAdd]
    exact ((isWitness_upperDecoderAt (by omega)).monotone ih).trans
      (upperDecoder_cutoff_le (by omega) N P)

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

/-- **The state code keeps separated states**, at a grade `j ≥ K` above the designated fields. -/
theorem sepInv_scode {K j : ℕ} (hF : FieldsLE K N T o) (hj : K ≤ j) {P : CProf I}
    (h : SepInv N T o P) : SepInv N T o (scode j P) := by
  obtain ⟨h0, ho, hT, hN⟩ := h
  have hhat : ∀ d, I.amalgam.toCellScheme.grade d ≤ K → hatS j P (Sum.inl d) = P (Sum.inl d) :=
    fun d hd ↦ hat_of_le (hd.trans hj)
  have hcode (f : Fin I.amalgam.card ⊕ Unit) :
      scode j P f = orbitMap j (hatS j P) (hatS j P f) := rfl
  have hkey : IsKey j (hatS j P) (hatS j P (Sum.inr ())) := isKey_apply_iff.mpr h0
  refine ⟨?_, ?_, fun x hx ↦ ?_, fun f hf hf0 k ↦ ?_⟩
  · rw [hcode, Ne, orbitMap_eq_bot_iff]; exact h0
  · rw [hcode, hcode, hhat o hF.2.2, ho]; rfl
  · obtain ⟨d, rfl, hd⟩ := hF.2.1 x hx
    rw [hcode, hcode, hhat d hd, hT _ hx]; rfl
  · rw [hcode, Ne, orbitMap_eq_bot_iff] at hf0
    have hle := hatS_le j P f
    have hP0 : P f ≠ ⊥ := fun h' ↦ hf0 (le_bot_iff.mp (h' ▸ hle))
    have hPf : hatS j P f = P f := by
      rcases f with d | z
      · by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
        · exact hat_of_le hd
        · exact absurd (hat_of_lt (_root_.not_le.mp hd)) hf0
      · rfl
    have hlt := hN f hf hP0 j
    rw [← hPf] at hlt
    have hcb := codeBlock_lt_codeBlock hf0 hkey hlt
    exact visibilityReplace_lt_of_block_lt (visibilityReplace_orbitMap hf0)
      (visibilityReplace_orbitMap h0) hcb k

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

end Sep

end VaughtConjecture.ProfileTower

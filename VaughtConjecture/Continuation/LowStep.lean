/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowTower
import VaughtConjecture.Continuation.LowExtension
import VaughtConjecture.Continuation.LowDonorRaising
import VaughtConjecture.Continuation.LowLowering

/-!
# Pieces of the LOW step

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step on the
amalgam); semantic contract, items 3, 4 and 8.

The capped lift from a coatom into the LOW layer over a good level of the profile tower needs only
the LOW step at the positive caps (`ProfileTower.Lvl.LowStep`,
`ProfileTower.Lvl.Good.cappedLift_lowS_of_lowStep`).  This file proves three of its pieces.

**Capping commutes with the frontier** (`Label.min_visibilityReplace_eq`,
`Label.min_frontier_eq`).  At a cap `h` self-visible at `K`, labels agreeing capped at `h` have
visibility replacements at `K` agreeing capped at `h`; so the frontiers of two profiles agreeing
capped at `h` at the owner and the lost top agree capped at `h`.

**The gap premise of donor raising from an active serving profile**
(`Label.min_frontier_le_of_isLowAt`, compiled in this repository).  If the serving profile `P` is
LOW and active, every donor top of `P` is at least `min c h`, where `c` is the frontier of any
labelling agreeing with `P` capped at `h` at the owner and the lost top (in the lift from the
private coatom, the prescribed private face): `min c h` is the frontier of `P` capped at `h`.  This
is the gap hypothesis of `StageType.IsLowFamily.donorRaisingGap` for the donor face of `P`, at
every designated top.  When `P` is not active nothing is to be raised: a coded profile with the
cutoff of `P` capped at `h` and the same proper donor fields is not active either
(`Label.not_lt_of_min_eq`).

**The faces of a profile lawful on the cut** (`ProfileTower.lawfulAt_left`,
`ProfileTower.lawfulAt_right`, compiled in this repository).  An amalgam profile lawful below the
two coatoms at the grade `K`, read on the cells of the private context (the left face of the seed)
or of the donor (the right face) and spliced with `⊥` above `K`, is lawful at `K` on that face in
the sense of donor raising (`H2.LawfulAt`).

**The coded cutoff** (`ProfileTower.exists_codedCutoff`, compiled in this repository).  For an
entry `P` of the LOW catalogue, a cap `h` self-visible and short at the grade, and an amalgam
profile `W` agreeing with the amalgam part of `P` capped at `h` and satisfying the frontier
condition when its donor maximum is below `min (P β) h`, the cutoff `min (P β) h` lies in the code
grid and makes the orbit code of `W` with that cutoff LOW.  A cap at most a value of the code grid
is in the code grid when it is self-visible and short (`Label.mem_codeGrid_of_le`).

So the LOW step from a coatom asks, beyond these pieces, the lift through the common face into the
other coatom with the frontier condition.

* From the donor coatom: the private frontier at most the cap
  (`StageType.IsSourceGapContextAt.exists_frontier_le`): it holds when the frontier of the lifted
  private face is already at most the cap, or when availability at the cells read by the owner
  above the threshold and by the lift above the owner is served by cells read above the threshold
  (`StageType.IsSourceGapContextAt.exists_lowering'`), in particular when `R_K (u r) < u o`
  (`StageType.IsSourceGapContextAt.serve_of_lt`).  Open: the case `h < u o ≤ R_K (u r)` with an
  unserved cell.
* From the private coatom: the private face, the owner and the lost top included, is prescribed
  (both are cells of the private coatom), and so are the serving profile and the cap, which come
  from the ambient section; so neither the lowering of the private frontier nor a choice of anchor
  avoiding the tie `h = R_K M` is available.  With the gap premise above, donor raising leaves a
  designated donor top at least the frontier or exactly at the cap, the second only at the tie
  (`Label.le_or_eq_of_raise`), where the LOW clause asks the frontier at most the cap
  (`Label.frontier_le_of_min_eq`).  Open: at the tie, a donor face lawful at `K`, literal on the
  root and agreeing with the serving profile capped at the cap, with every donor top (those
  determined by the root included) at least the prescribed frontier.  A witness fixing the donor
  maximum `M` fixes `R_K M`, so no witness image of a capped lift raises a top at the tie; a
  raising has to read the tops through a row separating them from the proper donor cells.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {K : ℕ}

/-- **Capping commutes with visibility replacement** at a cap self-visible at `K`. -/
theorem min_visibilityReplace_eq {x y h : Label.{u}} (hh : IsSelfVisible K h)
    (hxy : min x h = min y h) :
    min (visibilityReplace K K x) h = min (visibilityReplace K K y) h := by
  rcases lt_or_ge x h with hx | hx
  · rw [eq_of_min_eq_of_lt hxy hx]
  · have hy : h ≤ y := by
      have := hxy ▸ (min_eq_right hx).symm
      exact min_eq_right_iff.mp this.symm
    have hRx : h ≤ visibilityReplace K K x :=
      (hh.visibilityReplace_eq K).symm.le.trans (monotone_visibilityReplace le_rfl hx)
    have hRy : h ≤ visibilityReplace K K y :=
      (hh.visibilityReplace_eq K).symm.le.trans (monotone_visibilityReplace le_rfl hy)
    rw [min_eq_right hRx, min_eq_right hRy]

variable {X : Type*} {N : Finset X} {T : Set X} {o r β : X}

/-- **Capping commutes with the frontier**: profiles agreeing capped at `h` (self-visible at `K`)
at the owner and the lost top have frontiers agreeing capped at `h`. -/
theorem min_frontier_eq {a b : X → Label.{u}} {h : Label.{u}} (hh : IsSelfVisible K h)
    (ho : min (a o) h = min (b o) h) (hr : min (a r) h = min (b r) h) :
    min (frontier K o r a) h = min (frontier K o r b) h := by
  unfold frontier
  rw [min_assoc, ← min_self h, ← min_assoc (visibilityReplace K K (a r)), min_comm _ h,
    ← min_assoc, ho, min_visibilityReplace_eq hh hr, min_assoc (b o), min_comm h,
    min_assoc, min_self, ← min_assoc]

/-- **The gap premise from an active serving profile**: if `P` is LOW and active, every donor top
of `P` is at least `min c h`, for `c` the frontier of a labelling `f` agreeing with `P` capped at
`h` at the owner and the lost top. -/
theorem min_frontier_le_of_isLowAt {P f : X → Label.{u}} {h : Label.{u}}
    (hP : IsLowAt K N T o r β P) (hact : donorMax N P < P β) (hh : IsSelfVisible K h)
    (ho : min (f o) h = min (P o) h) (hr : min (f r) h = min (P r) h) :
    ∀ x ∈ T, min (frontier K o r f) h ≤ P x := fun x hx ↦ by
  rw [min_frontier_eq hh ho hr]
  exact (min_le_left _ _).trans ((le_max_right _ _).trans (hP hact x hx))

/-- **An inactive serving profile gives an inactive profile**: a profile agreeing with `P` capped
at `h` on the proper donor fields, with cutoff at most `min (P β) h`, is not active when `P` is
not. -/
theorem not_lt_of_min_eq {P u : X → Label.{u}} {h : Label.{u}}
    (hag : ∀ f ∈ N, min (u f) h = min (P f) h) (hβ : u β ≤ min (P β) h)
    (hin : ¬ donorMax N P < P β) : ¬ donorMax N u < u β := by
  intro hact
  have hMu : donorMax N u < h := hact.trans_le (hβ.trans (min_le_right _ _))
  rw [donorMax_eq_of_min_eq hag hMu] at hact
  exact hin (hact.trans_le (hβ.trans (min_le_left _ _)))

/-- **A self-visible short cap at most a value of the code grid lies in the code grid.** -/
theorem mem_codeGrid_of_le {k B : ℕ} {h y : Label.{u}} (hh : IsSelfVisible k h)
    (hs : IsShort k h) (hy : y ∈ codeGrid k B) (hhy : h ≤ y) : h ∈ codeGrid k B := by
  rcases mem_codeGrid.mp hy with rfl | ⟨b, hb, f, hf, rfl⟩
  · rw [le_bot_iff.mp hhy]; exact Finset.mem_insert_self _ _
  induction h using WithBot.recBotCoe with
  | bot => exact Finset.mem_insert_self _ _
  | coe h =>
    induction h using WithTop.recTopCoe with
    | top => exact absurd (WithBot.coe_le_coe.mp hhy) (not_le.mpr (WithTop.coe_lt_top _))
    | coe o =>
      have hok : (k : Ordinal.{u}) ≤ o % ω := isSelfVisible_coe.mp hh
      have hos : o % ω ≤ k := isShort_coe.mp hs
      have hle : o ≤ ω * (b : Ordinal.{u}) + f := by exact_mod_cast hhy
      have hlt : o < ω * ((b : Ordinal.{u}) + 1) := by
        rw [mul_add, mul_one]
        exact hle.trans_lt ((add_lt_add_iff_left _).mpr (natCast_lt_omega0 f))
      have hdiv : o / ω < (b : Ordinal.{u}) + 1 := (Ordinal.lt_mul_iff_div_lt omega0_ne_zero).mp hlt
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (hdiv.trans (by
        exact_mod_cast natCast_lt_omega0 (b + 1)))
      have hnb : n ≤ b := by
        rw [hn] at hdiv
        exact_mod_cast Order.lt_add_one_iff.mp hdiv
      have hmod : o % ω = k := le_antisymm hos hok
      refine mem_codeGrid.mpr (.inr ⟨n, hnb.trans hb, k, le_rfl, ?_⟩)
      have := Ordinal.div_add_mod o ω
      rw [hn, hmod] at this
      exact congrArg _ (congrArg _ this.symm)

end VaughtConjecture.Label

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The private face of a profile lawful below the first coatom**, spliced with `⊥` above `K`,
is lawful at `K` on the private context (the left face of the seed). -/
theorem lawfulAt_left {K : ℕ} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow (coatC, K) fun d ↦ W d) :
    H2.LawfulAt I.left K (I.left.toCellScheme.splice K (fun _ ↦ ⊥)
      fun i ↦ W (StageType.faceCell I.restrictFace_left i)) := by
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_left
  have h1 : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), K)
      (fun i ↦ W (StageType.faceCell I.restrictFace_left i)) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mpr ?_
    have hX : Prod.map (Finset.map (Coatom.left m)) id ((univ : Finset (Fin (m + 1))), K) =
        (coatC, K) := by
      rw [Prod.map_apply, Coatom.univ_map_left]; rfl
    rw [hX]
    exact hW
  exact ⟨(Rows.isLawfulBelow_congr fun d hd ↦ (CellScheme.splice_of_le hd.2).symm).mp h1,
    fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩

/-- **The donor face of a profile lawful below the second coatom**, spliced with `⊥` above `K`,
is lawful at `K` on the donor (the right face of the seed). -/
theorem lawfulAt_right {K : ℕ} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow (coatD, K) fun d ↦ W d) :
    H2.LawfulAt I.right K (I.right.toCellScheme.splice K (fun _ ↦ ⊥)
      fun i ↦ W (StageType.faceCell I.restrictFace_right i)) := by
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_right
  have h1 : I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), K)
      (fun i ↦ W (StageType.faceCell I.restrictFace_right i)) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mpr ?_
    have hX : Prod.map (Finset.map (Coatom.right m)) id ((univ : Finset (Fin (m + 1))), K) =
        (coatD, K) := by
      rw [Prod.map_apply, Coatom.univ_map_right]; rfl
    rw [hX]
    exact hW
  exact ⟨(Rows.isLawfulBelow_congr fun d hd ↦ (CellScheme.splice_of_le hd.2).symm).mp h1,
    fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩

variable {k : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The coded cutoff.**  Let `P` be an entry of the LOW catalogue at `k`, `h` self-visible and
short at `k`, and `W` an amalgam profile agreeing with the amalgam part of `P` capped at `h` that
satisfies the frontier condition when its donor maximum is below `min (P β) h` (the cutoff not
being a proper donor field nor a donor top).  Then the cutoff `min (P β) h` lies in the code grid,
agrees with that of `P` capped at `h`, and makes the orbit code of `W` with it LOW: activity of
the coded profile gives activity of `W` (the proper donor fields are below the cap, where the
coding is literal), and the orbit map, a witness bounded by `k`, carries the frontier condition. -/
theorem exists_codedCutoff {P : LProf I} (hP : P ∈ lowCat I k N T o r) {h : Label.{u}}
    (hh : IsSelfVisible k h) (hs : IsShort k h) {W : Prof I}
    (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h) (hN : Sum.inr () ∉ N) (hT : Sum.inr () ∉ T)
    (hfr : donorMax N (withCutoff W ⊥) < min (P (Sum.inr ())) h →
      ∀ x ∈ T, frontier k (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ withCutoff W ⊥ x) :
    ∃ β ∈ codeGrid k (bound I), min β h = min (P (Sum.inr ())) h ∧
      IsLowAt k N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) (withCutoff (orbitCode k W) β) := by
  obtain ⟨hPB, -, hPo, hPlow⟩ := mem_lowCat.mp hP
  set β := min (P (Sum.inr ())) h with hβ
  have hβB : β ∈ codeGrid k (bound I) := by
    rcases le_total (P (Sum.inr ())) h with hle | hle
    · rw [hβ, min_eq_left hle]; exact hPB _
    · rw [hβ, min_eq_right hle]; exact mem_codeGrid_of_le hh hs (hPB _) hle
  have hββ : min β h = min (P (Sum.inr ())) h := by rw [hβ, min_assoc, min_self]
  refine ⟨β, hβB, hββ, ?_⟩
  set u : LProf I := withCutoff (orbitCode k W) β with hu
  set V : LProf I := withCutoff W ⊥ with hV
  have hag : ∀ f, min (u f) h = min (P f) h := by
    rintro (d | z)
    · exact min_orbitCode_eq hh hs hPo hWP d
    · exact hββ
  refine isLowAt_of_min_eq hPlow hag (min_le_right _ _) fun hact x hx ↦ ?_
  have hMu : donorMax N u < h := hact.trans_le (min_le_right _ _)
  -- the coded profile and `W` agree on the proper donor fields, below the cap
  have hVu : ∀ f ∈ N, u f = V f := by
    rintro (d | z) hf
    · have hud : u (Sum.inl d) < h := (le_donorMax hf).trans_lt hMu
      have h1 : P (Sum.inl d) = u (Sum.inl d) := eq_of_min_eq_of_lt (hag _) hud
      have h2 : W d = P (Sum.inl d) := eq_of_min_eq_of_lt (hWP d).symm (h1 ▸ hud)
      exact h1.symm.trans h2.symm
    · cases z; exact absurd hf hN
  have hfV := hfr (by rw [← donorMax_congr hVu]; exact hact) x hx
  obtain ⟨x', rfl⟩ : ∃ x', x = Sum.inl x' := by
    rcases x with x' | z
    · exact ⟨x', rfl⟩
    · cases z; exact absurd hx hT
  have hσ := isWitness_orbitMap k W
  have hcomm : visibilityReplace k k (orbitMap k W (W r)) =
      orbitMap k W (visibilityReplace k k (W r)) :=
    (hσ.visibilityReplace_comm (W r) k (by rw [stepSuppressor_of_le le_rfl]; exact le_top) k
      le_rfl).symm
  unfold Label.frontier at hfV ⊢
  change min (orbitMap k W (W o)) (visibilityReplace k k (orbitMap k W (W r))) ≤
    orbitMap k W (W x')
  rw [hcomm, ← hσ.monotone.map_min]
  exact hσ.monotone hfV

/-! ### The LOW step from the donor coatom -/

variable {g : ℕ} {L : Lvl I g}

local notation "𝒞" => lowCat I (g + 1) N T o r

/-- **The LOW step from the donor coatom, except in the unserved case.**  Let the private context
(the left face of the seed) be a source-gap context of grade `g + 1` with the lost point last,
owner `o'` and lost top `r'`, whose amalgam copies are the owner `o` and the lost top `r` of the
LOW catalogue, let the proper donor fields and the donor tops be cells below the donor coatom, and
let the proper root cells (avoiding the lost point, not tops) be proper donor fields.  Given the
unserved case of the private frontier (`StageType.LowStepUnserved`), the LOW step holds from the
donor coatom.  The trace of the prescription on the common face is lifted into the private coatom
capped at the cap (bountifulness of the amalgam); when the serving profile is active, the private
face is replaced by a section with frontier at most the cap and the same root
(`StageType.IsSourceGapContextAt.exists_frontier_le_of_unserved`); the frontier condition then
holds at every donor top, at most the cap or, below the cap, by the LOW clause of the serving
profile (capping commutes with the frontier); the cutoff is coded by `exists_codedCutoff`. -/
theorem Lvl.Good.lowStep_donor (hL : L.Good) (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (hU : StageType.LowStepUnserved (g + 1) I.left (Fin.last m) o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N) :
    L.LowStep N T o r (Fin.castSucc (Fin.last m)) := by
  classical
  intro P hP h hh hsh hb w hw hwP
  obtain ⟨hPB, ⟨hPC, hPD⟩, hPo, hPlow⟩ := mem_lowCat.mp hP
  have hNinr : Sum.inr () ∉ N := fun hf ↦ by obtain ⟨d, hd, -⟩ := hNQ _ hf; cases hd
  have hTinr : Sum.inr () ∉ T := fun hf ↦ by obtain ⟨d, hd, -⟩ := hTQ _ hf; cases hd
  have hxP : Fin.castSucc (Fin.last m) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hyP : Fin.last (m + 1) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hxy : Fin.castSucc (Fin.last m) ≠ Fin.last (m + 1) := Seed.last_ne_castSucc.symm
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxP hyP hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  -- the prescription, on the amalgam
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  have ha : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_lowS_iff (C := 𝒞) (fun h' ↦ Seed.ne_univ_erase _
      (univ_subset_iff.mp h'.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (coatD, g + 1)) (Seed.ne_univ_erase _)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  have haP (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)) :
      min (a d) h = min (P (Sum.inl d)) h := hwP d hd.2 hd.1
  -- lift the trace on the common face into the private coatom, capped at `h` along `P`
  set O : Finset (Fin (m + 2)) × ℕ := (coatD ∩ coatC, g + 1) with hO
  have hOV : O ≤ (coatC, g + 1) := ⟨inter_subset_right, le_rfl⟩
  have hOU : O ≤ (coatD, g + 1) := ⟨inter_subset_left, le_rfl⟩
  have hlift : I.amalgam.rows.CappedLift hOV := I.isBountiful
    ⟨hOf, Nat.succ_pos g, show g + 1 ≤ #(coatD ∩ coatC) by rw [hOcard]; omega⟩
    ⟨I.erase_mem_faces hyP, Nat.succ_pos g, show g + 1 ≤ #(coatC) by rw [hcard]; omega⟩ hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P (Sum.inl d)) (ha.mono hOU) hPC
    fun d ↦ (haP d (I.amalgam.toCellScheme.below_mono hOU d.2)).symm
  -- the glued amalgam profile
  set A : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1) then q' ⟨d, hd'⟩
    else P (Sum.inl d) with hA
  have hAD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)) :
      A d = a d := dite_eq_left hd
  have hAC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)) :
      A d = q' ⟨d, hd⟩ := by
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)
    · rw [hAD d hdD]
      exact (hq'a ⟨d, ⟨subset_inter hdD.1 hd.1, hdD.2⟩⟩).symm
    · exact (dite_eq_right hdD).trans (dite_eq_left hd)
  have hAP (d : Fin I.amalgam.card) : min (A d) h = min (P (Sum.inl d)) h := by
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)
    · rw [hAD d hdD]; exact haP d hdD
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)
    · rw [hAC d hdC]; exact hq'P ⟨d, hdC⟩
    · have hAd : A d = P (Sum.inl d) := (dite_eq_right hdD).trans (dite_eq_right hdC)
      rw [hAd]
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ A d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hAD d hd).symm).mp ha
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ A d := by
    convert hq' using 1
    funext d
    exact hAC d.1 d.2
  -- the agreement and the coded cutoff, for a profile equal to `A` below the donor coatom
  have hfinish (W : Prof I) (hWC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ W d)
      (hWD : ∀ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : donorMax N (withCutoff W ⊥) < min (P (Sum.inr ())) h →
        ∀ x ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ withCutoff W ⊥ x) :
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last m)) →
            W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        IsLowAt (g + 1) N T (Sum.inl o) (Sum.inl r) (Sum.inr ())
          (withCutoff (orbitCode (g + 1) W) β) := by
    obtain ⟨β, hβB, hβ, hlow⟩ := exists_codedCutoff hP hh hsh hWP hNinr hTinr hfr
    exact ⟨W, β, ⟨hWC, (Rows.isLawfulBelow_congr fun d hd ↦ hWD d hd).mpr hAlD⟩,
      fun d hd hds ↦ (hWD d ⟨hds, hd⟩).trans (hAD d ⟨hds, hd⟩), hWP, hβB, hβ, hlow⟩
  by_cases hact : donorMax N (withCutoff A ⊥) < min (P (Sum.inr ())) h
  swap
  · exact hfinish A hAlC (fun _ _ ↦ rfl) hAP fun h' ↦ absurd h' hact
  -- the private face, lowered
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_left
  have hX : Prod.map (Finset.map (Coatom.left m)) id ((univ : Finset (Fin (m + 1))), g + 1) =
      (coatC, g + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_left]; rfl
  set fc : Fin I.left.card → Fin I.amalgam.card := StageType.faceCell I.restrictFace_left with hfc
  set ut : Fin I.left.card → Label.{u} := fun i ↦ A (fc i) with hut_def
  have hut : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), g + 1)
      (fun i ↦ ut i) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ A).mpr ?_
    rw [hX]
    exact hAlC
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ → ut i ≤ h := fun i hi hl ht ↦
    ((le_donorMax (a := withCutoff A ⊥) (hNroot i hi hl ht)).trans hMh.le)
  obtain ⟨vt, hvt, hvcap, hvroot, hvfr⟩ :=
    hs.exists_frontier_le_of_unserved I.isLegal_left hU hut hh hb hroot
  have hinj : Function.Injective fc := Scheme.faceCell_injective he
  set vt' : Fin I.left.card → Label.{u} := fun i ↦
    if I.left.toCellScheme.grade i ≤ g + 1 then vt i else ut i with hvt'
  set W : Prof I := Function.extend fc vt' A with hW
  have hWf (i : Fin I.left.card) : W (fc i) = vt' i := hinj.extend_apply _ _ i
  have hWle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ g + 1) :
      W (fc i) = vt i := (hWf i).trans (ite_eq_left hi)
  have hWgt (i : Fin I.left.card) (hi : ¬ I.left.toCellScheme.grade i ≤ g + 1) :
      W (fc i) = ut i := (hWf i).trans (ite_eq_right hi)
  have hWD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)) :
      W d = A d := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      have hgi : I.left.toCellScheme.grade i ≤ g + 1 := by
        have := hd.2
        rwa [CellScheme.gradedIndex_snd, StageType.grade_faceCell] at this
      have hli : Fin.last m ∉ I.left.toCellScheme.scope i := by
        intro hm
        have h1 : Fin.castSucc (Fin.last m) ∈ I.amalgam.toCellScheme.scope (fc i) := by
          rw [hfc, StageType.scope_faceCell]
          exact mem_map_of_mem _ hm
        have h2 := hd.1 h1
        simp at h2
      rw [hWle i hgi]
      exact hvroot i hgi hli
    · exact Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hex ⟨i, hi⟩
  have hWC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.left.rows) (X := ((univ : Finset (Fin (m + 1))), g + 1))
      (w := fun i ↦ vt i) (w' := fun i ↦ W (fc i))
      fun i hi ↦ (hWle i (show I.left.toCellScheme.grade i ≤ g + 1 from hi.2)).symm).mp hvt
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      by_cases hgi : I.left.toCellScheme.grade i ≤ g + 1
      · rw [hWle i hgi, hvcap i hgi]; exact hAP _
      · rw [hWgt i hgi]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hex ⟨i, hi⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWC hWD hWP fun _ x hx ↦ ?_
  -- the frontier condition
  obtain ⟨d, rfl, hdD⟩ := hTQ x hx
  have hgo : I.left.toCellScheme.grade o' ≤ g + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ g + 1 :=
    hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  have hfrW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ h := by
    unfold Label.frontier
    change min (W o) (visibilityReplace (g + 1) (g + 1) (W r)) ≤ h
    rw [ho, hr, hWle o' hgo, hWle r' hgr]
    exact hvfr
  change frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ W d
  rw [hWD d hdD]
  rcases le_or_gt h (A d) with hhA | hAh
  · exact hfrW.trans hhA
  -- below the cap: the serving profile is active and reads the donor top
  have hAPd : P (Sum.inl d) = A d := eq_of_min_eq_of_lt (hAP d) hAh
  have hNP : ∀ f ∈ N, P f = withCutoff A ⊥ f := by
    intro f hf
    obtain ⟨e, rfl, -⟩ := hNQ f hf
    exact eq_of_min_eq_of_lt (hAP e) ((le_donorMax (a := withCutoff A ⊥) hf).trans_lt hMh)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [donorMax_congr hNP]
    exact hact.trans_le (min_le_left _ _)
  have hPx := (le_max_right _ _).trans (hPlow hPact _ hx)
  have hmin := min_frontier_eq (K := g + 1) (o := Sum.inl o) (r := Sum.inl r)
    (a := withCutoff W ⊥) (b := P) hh (hWP o) (hWP r)
  have hfP : frontier (g + 1) (Sum.inl o) (Sum.inl r) P < h := hPx.trans_lt (hAPd ▸ hAh)
  have h2 : min (frontier (g + 1) (Sum.inl o) (Sum.inl r) P) h =
      min (frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥)) h := hmin.symm
  have hfW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) =
      frontier (g + 1) (Sum.inl o) (Sum.inl r) P := eq_of_min_eq_of_lt h2 hfP
  rw [hfW, ← hAPd]
  exact hPx

end VaughtConjecture.ProfileTower

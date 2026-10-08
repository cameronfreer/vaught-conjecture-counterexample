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

**The LOW step, assembled** (`ProfileTower.Lvl.Good.lowStep_donor`,
`ProfileTower.Lvl.Good.lowStep_private`, `ProfileTower.Lvl.Good.cappedLift_lowS_of_unserved_tie`,
compiled in this repository).  For the LOW designations (owner and lost top the copies of those of
the private context, donor tops the copies of the tops of the donor, proper donor fields the
copies of the proper cells of the donor of grade at most `K`, all below the donor coatom), the
LOW step from either coatom, hence the capped lift into the LOW layer at the grade `K`, follows
from exactly two named open cases:

* `StageType.LowStepUnserved` (from the donor coatom): a lifted private face with
  `h < u o ≤ R_K (u r)` and a cell read by the owner above the threshold and by the lift above the
  owner, served only by cells read at most the threshold.  Otherwise the lift through the common
  face (bountifulness of the amalgam), the lowering of the lost top
  (`StageType.IsSourceGapContextAt.exists_frontier_le_of_unserved`), the gluing on the amalgam
  and the coded cutoff give the step.
* `StageType.LowStepTie` (from the private coatom): a donor face reading every donor top off the
  root at least at the prescribed private frontier `c > h`, at the tie `h = R_K M` or when a donor
  top is determined by the root.  Otherwise donor raising (`StageType.IsLowFamily.exists_raised`),
  the root tops (at least `c` by the strict source gaps), the gluing and the coded cutoff give the
  step; when `c ≤ h` the capped agreement with the serving profile suffices.

From the private coatom the private face, the owner and the lost top included, is prescribed,
and so are the serving profile and the cap, which come from the ambient section; so neither the
lowering of the private frontier nor a choice of anchor avoiding the tie is available.  A witness
fixing the donor maximum `M` fixes `R_K M`, so no witness image of a capped lift raises a top at
the tie.  A raising has to read the tops through a row separating them from the proper donor cells:
the row of a top cell `Z` of the donor reads every top below `Z` above the replaced readings of the
proper cells (`StageType.visibilityReplace_rowAt_lt_of_top`, compiled in this repository); a
raising through it, literal on the root and agreeing with the ambient capped at the cap, is not
constructed here.

Both open cases are statements about one face: the unserved case about the private context
alone, the tie case about the donor alone given the prescribed private frontier.  The gluing of
the two faces on the amalgam and the layers below are compiled above; so the two cases do not come
from the two-coatom geometry, and they reappear when the donor is attached along a smaller root
(the tie case as a relative lift of the donor from that root, with the frontier read from the
context section).

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

/-! ### The LOW step from the private coatom: the donor face -/

namespace VaughtConjecture.StageType

open Finset Label H2 FieldAdmission

variable {α : Ordinal.{u}} {k : ℕ}

variable (K : ℕ) (t' tb : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
  (hp : restrictFace Fin.castSuccEmb t' = some p) (hpb : restrictFace Fin.castSuccEmb tb = some p)
  (o r : Fin t'.card) in
/-- **The tie case of the donor face** (open): for a private face `f` and a donor face `R`, lawful
at `K`, agreeing on the root capped at a cap `h` below the frontier `c` of `f`, with every donor top
off the root read by `R` at least at `h`, if the cap is the replaced low maximum of `R` (the tie)
or some donor top off the root is determined by the root, some donor face lawful at `K`, literal on
the root and agreeing with `R` capped at `h`, reads every donor top off the root at least at `c`.
-/
def LowStepTie : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → h < c → ∀ {R : Fin tb.card → Label.{u}}
    {f : Fin t'.card → Label.{u}}, LawfulAt tb K R → LawfulAt t' K f →
    (∀ x, min (f (faceCell hp x)) h = min (R (faceCell hpb x)) h) →
    c = min (f o) (visibilityReplace K K (f r)) →
    (∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
      t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t) →
    (h = visibilityReplace K K
        (((univ.filter fun x ↦ tb.label x ≠ ⊤).filter fun x ↦ tb.toCellScheme.grade x ≤ K).sup R) ∨
      ∃ t, tb.label t = ⊤ ∧ tb.toCellScheme.grade t ≤ K ∧
        t ∉ tb.toScheme.visibleCells Fin.castSuccEmb ∧ RootDetAt tb K t) →
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ x, W (faceCell hpb x) = f (faceCell hp x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
        t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → c ≤ W t

variable {K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The donor face from the private coatom, except in the tie case.**  At a LOW family, for a
private face `f` and a donor face `R` lawful at `K` agreeing on the root capped at `h`, with the
frontier `c` of `f` above `h` and every donor top off the root read by `R` at least at `h`, some
donor face lawful at `K`, literal on the root and agreeing with `R` capped at `h`, reads every donor
top off the root at least at `c`: by donor raising with the gap (`IsLowFamily.donorRaisingGap`)
off the tie, where the second outcome would put a top at most the replaced low maximum, below
the cap; and by `LowStepTie` at the tie or at a donor top determined by the root. -/
theorem IsLowFamily.exists_raised (hF : IsLowFamily K t' tb p o r)
    (hT : LowStepTie K t' tb hF.face_private hF.face_donor o r) {h c : Label.{u}}
    (hh : IsSelfVisible K h) (hb : ⊥ < h) (hhc : h < c) {R : Fin tb.card → Label.{u}}
    {f : Fin t'.card → Label.{u}} (hR : LawfulAt tb K R) (hf : LawfulAt t' K f)
    (hag : ∀ x, min (f (faceCell hF.face_private x)) h = min (R (faceCell hF.face_donor x)) h)
    (hlow : ∀ x, tb.label x ≠ ⊤ → tb.toCellScheme.grade x ≤ K → R x < h)
    (hc : c = min (f o) (visibilityReplace K K (f r)))
    (htop : ∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
      t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ x, W (faceCell hF.face_donor x) = f (faceCell hF.face_private x)) ∧
      (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
        t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → c ≤ W t := by
  classical
  set Lo := (univ.filter fun x ↦ tb.label x ≠ ⊤).filter fun x ↦ tb.toCellScheme.grade x ≤ K
    with hLo
  by_cases hres : h = visibilityReplace K K (Lo.sup R) ∨ ∃ t, tb.label t = ⊤ ∧
      tb.toCellScheme.grade t ≤ K ∧ t ∉ tb.toScheme.visibleCells Fin.castSuccEmb ∧ RootDetAt tb K t
  · exact hT hh hhc hR hf hag hc htop hres
  obtain ⟨hnt, hnrd⟩ := not_or.mp hres
  push Not at hnrd
  set Tops : Finset (Fin tb.card) := univ.filter fun x ↦ tb.label x = ⊤ ∧
    tb.toCellScheme.grade x ≤ K ∧ x ∉ tb.toScheme.visibleCells Fin.castSuccEmb ∧
      ¬ RootDetAt tb K x with hTops
  have hdes : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops :=
    fun x h1 h2 h3 h4 ↦ mem_filter.mpr ⟨mem_univ _, h1, h2, h3, h4⟩
  -- the frontier `c` is self-visible, and the root tops of `f` are at least `c`
  have hfo := (frontier_le_lawfulAt hF.isLegal_private hF.isSourceGapContextAt hf)
  have hcv : IsSelfVisible K c := by
    rw [hc]
    rcases min_choice (f o) (visibilityReplace K K (f r)) with h1 | h1 <;> rw [h1]
    · exact hfo.1
    · exact visibilityReplace_self_visibilityReplace le_rfl _
  obtain ⟨W, hW, hWr, hWR, hWt⟩ := hF.donorRaisingGap hdes hh hcv hR hf hag (fun a ha ↦ by
      rw [hc]
      have := hfo.2 (faceCell hF.face_private a) (by rw [label_faceCell]; exact ha.1) ha.2
      exact this)
    fun t ht _ ↦ by
      obtain ⟨-, h1, h2, h3, -⟩ := mem_filter.mp ht
      exact (min_le_right _ _).trans (htop t h1 h2 h3)
  refine ⟨W, hW, hWr, hWR, fun t h1 h2 h3 ↦ ?_⟩
  have hRt := htop t h1 h2 h3
  have hWh : h ≤ W t := by
    have := hWR t
    rw [min_eq_right hRt] at this
    exact min_eq_right_iff.mp this
  -- the low maximum of `W` is that of `R`, below the cap, and off the tie its replacement is too
  have hLoR : Lo.sup R < h := (Finset.sup_lt_iff hb).mpr fun x hx ↦ by
    obtain ⟨h1, h2⟩ := mem_filter.mp hx
    exact hlow x (mem_filter.mp h1).2 h2
  have hLoW : Lo.sup W = Lo.sup R := Finset.sup_congr rfl fun x hx ↦
    (eq_of_min_eq_of_lt (hWR x).symm ((Finset.le_sup (f := R) hx).trans_lt hLoR))
  have hRK : visibilityReplace K K (Lo.sup R) < h :=
    lt_of_le_of_ne (visibilityReplace_le_of_le le_rfl hh hLoR.le) (Ne.symm hnt)
  rcases hWt t (mem_filter.mpr ⟨mem_univ _, h1, h2, h3, hnrd t h1 h2 h3⟩) hRt with h4 | h4
  · exact h4
  · rw [hLoW] at h4
    exact absurd (hWh.trans h4) (not_le.mpr hRK)

end VaughtConjecture.StageType

/-! ### The LOW step from the private coatom -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {g : ℕ} {L : Lvl I g}

local notation "𝒞" => lowCat I (g + 1) N T o r

/-- **The LOW step from the private coatom, except in the tie case.**  Let the private context be
a source-gap context of grade `g + 1` with the lost point last, owner `o'` and lost top `r'`
(copies `o`, `r`), the donor of top grade at most `g + 1`, the donor tops the copies of the tops of
the donor, the copies of the proper donor cells of grade at most `g + 1` proper donor fields, and
the proper donor fields cells below the donor coatom.  Given the tie case of the donor face
(`StageType.LowStepTie`), the LOW step holds from the private coatom.  The trace of the
prescription on the common face is lifted into the donor coatom capped at the cap; when the
serving profile is active and the prescribed private frontier `c` is above the cap, the donor face
is replaced by one reading every donor top off the root at least at `c`
(`StageType.IsLowFamily.exists_raised`; the root tops are at least `c` by the strict source gaps);
when `c` is at most the cap, the capped agreement with the serving profile already gives the
frontier condition; the cutoff is coded by `exists_codedCutoff`. -/
theorem Lvl.Good.lowStep_private (hL : L.Good) (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1)
    (hTie : StageType.LowStepTie (g + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ g + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N) :
    L.LowStep N T o r (Fin.last (m + 1)) := by
  classical
  intro P hP h hh hsh hb w hw hwP
  obtain ⟨hPB, ⟨hPC, hPD⟩, hPo, hPlow⟩ := mem_lowCat.mp hP
  have hNinr : Sum.inr () ∉ N := fun hf ↦ by obtain ⟨d, hd, -⟩ := hNQ _ hf; cases hd
  have hTinr : Sum.inr () ∉ T := fun hf ↦ by obtain ⟨d, -, hd⟩ := hTR _ hf; cases hd
  have hxP : Fin.last (m + 1) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hyP : Fin.castSucc (Fin.last m) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hxy : Fin.last (m + 1) ≠ Fin.castSucc (Fin.last m) := Seed.last_ne_castSucc
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxP hyP hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  have ha : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_lowS_iff (C := 𝒞) (fun h' ↦ Seed.ne_univ_erase _
      (univ_subset_iff.mp h'.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (coatC, g + 1)) (Seed.ne_univ_erase _)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  have haP (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)) :
      min (a d) h = min (P (Sum.inl d)) h := hwP d hd.2 hd.1
  set O : Finset (Fin (m + 2)) × ℕ := (coatC ∩ coatD, g + 1) with hO
  have hOV : O ≤ (coatD, g + 1) := ⟨inter_subset_right, le_rfl⟩
  have hOU : O ≤ (coatC, g + 1) := ⟨inter_subset_left, le_rfl⟩
  have hlift : I.amalgam.rows.CappedLift hOV := I.isBountiful
    ⟨hOf, Nat.succ_pos g, show g + 1 ≤ #(coatC ∩ coatD) by rw [hOcard]; omega⟩
    ⟨I.erase_mem_faces hyP, Nat.succ_pos g, show g + 1 ≤ #(coatD) by rw [hcard]; omega⟩ hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P (Sum.inl d)) (ha.mono hOU) hPD
    fun d ↦ (haP d (I.amalgam.toCellScheme.below_mono hOU d.2)).symm
  set A : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) then q' ⟨d, hd'⟩
    else P (Sum.inl d) with hA
  have hAC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)) :
      A d = a d := dite_eq_left hd
  have hAD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)) :
      A d = q' ⟨d, hd⟩ := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)
    · rw [hAC d hdC]
      exact (hq'a ⟨d, ⟨subset_inter hdC.1 hd.1, hdC.2⟩⟩).symm
    · exact (dite_eq_right hdC).trans (dite_eq_left hd)
  have hAP (d : Fin I.amalgam.card) : min (A d) h = min (P (Sum.inl d)) h := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)
    · rw [hAC d hdC]; exact haP d hdC
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)
    · rw [hAD d hdD]; exact hq'P ⟨d, hdD⟩
    · have hAd : A d = P (Sum.inl d) := (dite_eq_right hdC).trans (dite_eq_right hdD)
      rw [hAd]
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ A d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hAC d hd).symm).mp ha
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ A d := by
    convert hq' using 1
    funext d
    exact hAD d.1 d.2
  have hfinish (W : Prof I) (hWD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ W d)
      (hWC : ∀ d ∈ I.amalgam.toCellScheme.below (coatC, g + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : donorMax N (withCutoff W ⊥) < min (P (Sum.inr ())) h →
        ∀ x ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ withCutoff W ⊥ x) :
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) →
            W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        IsLowAt (g + 1) N T (Sum.inl o) (Sum.inl r) (Sum.inr ())
          (withCutoff (orbitCode (g + 1) W) β) := by
    obtain ⟨β, hβB, hβ, hlow⟩ := exists_codedCutoff hP hh hsh hWP hNinr hTinr hfr
    exact ⟨W, β, ⟨(Rows.isLawfulBelow_congr fun d hd ↦ hWC d hd).mpr hAlC, hWD⟩,
      fun d hd hds ↦ (hWC d ⟨hds, hd⟩).trans (hAC d ⟨hds, hd⟩), hWP, hβB, hβ, hlow⟩
  by_cases hact : donorMax N (withCutoff A ⊥) < min (P (Sum.inr ())) h
  swap
  · exact hfinish A hAlD (fun _ _ ↦ rfl) hAP fun h' ↦ absurd h' hact
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hNP : ∀ f ∈ N, P f = withCutoff A ⊥ f := by
    intro f hf
    obtain ⟨e, rfl, -⟩ := hNQ f hf
    exact eq_of_min_eq_of_lt (hAP e) ((le_donorMax (a := withCutoff A ⊥) hf).trans_lt hMh)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [donorMax_congr hNP]
    exact hact.trans_le (min_le_left _ _)
  -- the prescribed private frontier
  set c := frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff A ⊥) with hc_def
  have hgap : ∀ x ∈ T, min c h ≤ P x := fun x hx ↦
    min_frontier_le_of_isLowAt hPlow hPact hh (hAP o) (hAP r) x hx
  by_cases hch : c ≤ h
  · refine hfinish A hAlD (fun _ _ ↦ rfl) hAP fun _ x hx ↦ ?_
    obtain ⟨t, -, rfl⟩ := hTR x hx
    have h1 := hgap _ hx
    rw [min_eq_left hch] at h1
    have h2 : min c h ≤ min (A (StageType.faceCell I.restrictFace_right t)) h := by
      rw [hAP]; exact le_min ((min_le_left _ _).trans h1) (min_le_right _ _)
    rw [min_eq_left hch] at h2
    exact h2.trans (min_le_left _ _)
  have hhc : h < c := _root_.not_le.mp hch
  -- the donor raising
  have hF : StageType.IsLowFamily (g + 1) I.left I.right I.face o' r' :=
    ⟨I.isLegal_left, I.isLegal_right, I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩
  set fcL := StageType.faceCell I.restrictFace_left with hfcL
  set fcR := StageType.faceCell I.restrictFace_right with hfcR
  set f : Fin I.left.card → Label.{u} := I.left.toCellScheme.splice (g + 1) (fun _ ↦ ⊥)
    fun i ↦ A (fcL i) with hf_def
  set R : Fin I.right.card → Label.{u} := I.right.toCellScheme.splice (g + 1) (fun _ ↦ ⊥)
    fun j ↦ P (Sum.inl (fcR j)) with hR_def
  have hf : H2.LawfulAt I.left (g + 1) f := lawfulAt_left hAlC
  have hR : H2.LawfulAt I.right (g + 1) R := lawfulAt_right (W := amal P) hPD
  have hfle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ g + 1) : f i = A (fcL i) :=
    CellScheme.splice_of_le hi
  have hRle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ g + 1) :
      R j = P (Sum.inl (fcR j)) := CellScheme.splice_of_le hj
  have hroot (x : Fin I.face.card) :
      fcL (StageType.faceCell I.restrictFace_face_left x) =
        fcR (StageType.faceCell I.restrictFace_face_right x) :=
    StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right x
  have hag (x : Fin I.face.card) :
      min (f (StageType.faceCell I.restrictFace_face_left x)) h =
        min (R (StageType.faceCell I.restrictFace_face_right x)) h := by
    have hg : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) =
        I.right.toCellScheme.grade (StageType.faceCell I.restrictFace_face_right x) := by
      rw [StageType.grade_faceCell, StageType.grade_faceCell]
    by_cases hx : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) ≤ g + 1
    · rw [hfle _ hx, hRle _ (hg ▸ hx), hroot]; exact hAP _
    · rw [hf_def, hR_def, CellScheme.splice_of_lt (_root_.not_le.mp hx),
        CellScheme.splice_of_lt (_root_.not_le.mp (hg ▸ hx))]
  have hgo : I.left.toCellScheme.grade o' ≤ g + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ g + 1 :=
    hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  have hcf : c = min (f o') (visibilityReplace (g + 1) (g + 1) (f r')) := by
    rw [hc_def, hfle o' hgo, hfle r' hgr, ← ho, ← hr]; rfl
  have htop : ∀ t, I.right.label t = ⊤ → I.right.toCellScheme.grade t ≤ g + 1 →
      t ∉ I.right.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t := fun t ht hg _ ↦ by
    rw [hRle t hg]
    have := hgap _ (hTtop t ht)
    rwa [min_eq_right hhc.le] at this
  have hlow : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ g + 1 → R t < h :=
    fun t ht hg ↦ by
      rw [hRle t hg, hNP _ (hLoN t ht hg)]
      exact (le_donorMax (a := withCutoff A ⊥) (hLoN t ht hg)).trans_lt hMh
  obtain ⟨Wt, hWt, hWtr, hWtR, hWtc⟩ :=
    hF.exists_raised hTie hh hb hhc hR hf hag hlow hcf htop
  -- glue the raised donor face on the amalgam
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_right
  have hX : Prod.map (Finset.map (Coatom.right m)) id ((univ : Finset (Fin (m + 1))), g + 1) =
      (coatD, g + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_right]; rfl
  have hinj : Function.Injective fcR := Scheme.faceCell_injective he
  set wt' : Fin I.right.card → Label.{u} := fun j ↦
    if I.right.toCellScheme.grade j ≤ g + 1 then Wt j else A (fcR j) with hwt'
  set W : Prof I := Function.extend fcR wt' A with hW
  have hWf (j : Fin I.right.card) : W (fcR j) = wt' j := hinj.extend_apply _ _ j
  have hWle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ g + 1) :
      W (fcR j) = Wt j := (hWf j).trans (ite_eq_left hj)
  have hWgt (j : Fin I.right.card) (hj : ¬ I.right.toCellScheme.grade j ≤ g + 1) :
      W (fcR j) = A (fcR j) := (hWf j).trans (ite_eq_right hj)
  have hWC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)) :
      W d = A d := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      have hgj : I.right.toCellScheme.grade j ≤ g + 1 := by
        have := hd.2
        rwa [CellScheme.gradedIndex_snd, StageType.grade_faceCell] at this
      have hlj : Fin.last m ∉ I.right.toCellScheme.scope j := by
        intro hm
        have h1 : Fin.last (m + 1) ∈ I.amalgam.toCellScheme.scope (fcR j) := by
          rw [hfcR, StageType.scope_faceCell]
          exact mem_map.mpr ⟨Fin.last m, hm, by simp [Coatom.right]⟩
        have h2 := hd.1 h1
        simp at h2
      obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_right hlj
      rw [hWle _ hgj, hWtr x, ← hroot]
      have hgx : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) ≤
          g + 1 := by
        rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_right]
        exact hgj
      exact hfle _ hgx
    · exact Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
  have hWD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.right.rows)
      (X := ((univ : Finset (Fin (m + 1))), g + 1)) (w := fun j ↦ Wt j) (w' := fun j ↦ W (fcR j))
      fun j hj ↦ (hWle j (show I.right.toCellScheme.grade j ≤ g + 1 from hj.2)).symm).mp hWt.1
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      by_cases hgj : I.right.toCellScheme.grade j ≤ g + 1
      · rw [hWle j hgj, hWtR j, hRle j hgj]
      · rw [hWgt j hgj]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWD hWC hWP fun _ x hx ↦ ?_
  -- the frontier condition: the frontier is the prescribed one, at most every donor top
  have hob : o ∈ I.amalgam.toCellScheme.below (coatC, g + 1) := by
    rw [ho, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgo⟩
  have hrb : r ∈ I.amalgam.toCellScheme.below (coatC, g + 1) := by
    rw [hr, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgr⟩
  have hfW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) = c := by
    rw [hc_def]
    unfold Label.frontier
    change min (W o) (visibilityReplace (g + 1) (g + 1) (W r)) =
      min (A o) (visibilityReplace (g + 1) (g + 1) (A r))
    rw [hWC o hob, hWC r hrb]
  rw [hfW]
  obtain ⟨t, ht, rfl⟩ := hTR x hx
  have hgt : I.right.toCellScheme.grade t ≤ g + 1 :=
    (StageType.topGrade_le_iff.mp htb) t ht
  change c ≤ W (fcR t)
  by_cases hvis : t ∈ I.right.toScheme.visibleCells Fin.castSuccEmb
  · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq I.restrictFace_face_right hvis
    rw [hWle _ hgt, hWtr y, hcf]
    have hfo := H2.frontier_le_lawfulAt I.isLegal_left hs hf
    refine hfo.2 _ ?_ (StageType.last_notMem_scope_faceCell I.restrictFace_face_left y)
    rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_right]
    exact ht
  · rw [hWle _ hgt]
    exact hWtc t ht hgt hvis

/-- **The capped lift from either coatom into the LOW layer over a good level, from the two
named cases.**  Under the designations of `ProfileTower.Lvl.Good.lowStep_donor` and
`ProfileTower.Lvl.Good.lowStep_private`, the unserved case of the private frontier
(`StageType.LowStepUnserved`) and the tie case of the donor face (`StageType.LowStepTie`) give the
capped lift from either coatom at the grade `g + 1` into `(univ, g + 1)`
(`ProfileTower.Lvl.Good.cappedLift_lowS_of_lowStep`). -/
theorem Lvl.Good.cappedLift_lowS_of_unserved_tie (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1)
    (hU : StageType.LowStepUnserved (g + 1) I.left (Fin.last m) o' r')
    (hTie : StageType.LowStepTie (g + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N)
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ g + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  refine hL.cappedLift_lowS_of_lowStep hgm hx ?_
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact hL.lowStep_private hgm hs htb hTie ho hr hNQ hTR hTtop hLoN
  · rw [Finset.mem_singleton.mp hx']
    exact hL.lowStep_donor hgm hs hU ho hr hNQ hTQ hNroot

end VaughtConjecture.ProfileTower

/-! ### The donor-side source gap -/

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The source gap at a top cell**: in a stage type `t`, the row of a cell `Z` labelled `⊤`
reads every cell `x` below `Z` labelled `⊤` strictly above the replacement, at the grade of `Z`,
of its reading of every cell `y` below `Z` with a proper label.  The labels below `Z` are the
images of the row of `Z` under the witness of the locality of the labels at `Z`, which commutes
with the replacement; a proper label has a proper replacement.  At a top cell of the donor of
graded index `(univ, K)` this is the source gap through which a raising of the donor tops at the
tie can read them apart from the proper donor cells. -/
theorem visibilityReplace_rowAt_lt_of_top {t : StageType.{u} α n} {Z : Fin t.card}
    (hZ : t.label Z = ⊤) {x y : Fin t.card}
    (hx : x ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z))
    (hy : y ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) (hxt : t.label x = ⊤)
    (hyt : t.label y ≠ ⊤) :
    visibilityReplace (t.toCellScheme.grade Z) (t.toCellScheme.grade Z) (t.rowAt Z y) <
      t.rowAt Z x := by
  obtain ⟨g, σ, hσ, heq⟩ := t.isLawful.locality Z
  have hread (d : Fin t.card) (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) :
      min (t.label d) (t.label Z) = min (σ (t.rowAt Z d)) (g (t.toCellScheme.grade d)) := by
    rw [Scheme.rowAt_of_mem hd]
    exact heq ⟨d, hd⟩
  have hgZ : g (t.toCellScheme.grade Z) = ⊤ := by
    have h := (hread Z (t.toCellScheme.mem_below_gradedIndex Z)).symm
    rw [hZ, min_self] at h
    exact (_root_.min_eq_top.mp h).2
  have hlab (d : Fin t.card) (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) :
      t.label d = σ (t.rowAt Z d) := by
    have h := hread d hd
    have hgd : g (t.toCellScheme.grade d) = ⊤ :=
      top_le_iff.mp (hgZ ▸ hσ.antitone (show t.toCellScheme.grade d ≤ t.toCellScheme.grade Z
        from hd.2))
    rwa [hZ, min_top_right, hgd, min_top_right] at h
  refine lt_of_not_ge fun hle ↦ hyt ?_
  have h1 : σ (t.rowAt Z x) ≤ σ (visibilityReplace (t.toCellScheme.grade Z)
      (t.toCellScheme.grade Z) (t.rowAt Z y)) := hσ.monotone hle
  rw [← hlab x hx, hxt, hσ.visibilityReplace_comm _ _ (by rw [hgZ]; exact le_top) _ le_rfl,
    ← hlab y hy, top_le_iff, visibilityReplace_eq_top_iff] at h1
  exact h1

end VaughtConjecture.StageType

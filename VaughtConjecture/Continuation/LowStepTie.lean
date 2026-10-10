/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStep
import VaughtConjecture.Extension.CappedDecoder
import VaughtConjecture.Continuation.H2OwnerGeneral

/-!
# The tie case of the LOW step through a top cell of the donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step from the
private coatom at the tie); semantic contract, items 3, 4 and 8.

At the tie of donor raising no witness image of a capped lift raises a donor top: a witness fixing
the donor maximum fixes its replacement.  The donor is read instead through the row of a cell `Z`
labelled `⊤` of graded index `(univ, K)`, the **template** `V = row_Z`: it reads every top above
the replacements of its readings of the proper cells (`StageType.visibilityReplace_rowAt_lt_of_top`,
the donor-side source gap), so a threshold `θ_b`, the largest such replacement, separates the tops
from the proper cells in `V`.

**The raise map** (`Label.raiseMap`, `Label.isWitness_raiseMap`, in
`VaughtConjecture.Continuation.LowGapRaise`): for a map `θ` fixing `⊥`, monotone, commuting with
visibility replacement and keeping its bottom, a threshold `θ_b` and a cap `c`, both self-visible
at `K`, the map equal to `θ` at and below `θ_b`, to `max (θ v) c` above, and `⊥` where `θ` is `⊥`,
is a witness bounded by `K`.

**The raise through the template** (`StageType.exists_raised_of_dominated`, compiled in this
repository).  Let `W₁` be a section of the donor lawful at `K` (bottom above `K`) dominated at `Z`:
every cell of grade at most `K` is read by `W₁` at most at `Z`.  With `θ` the
capped decoder of `W₁` at `Z` (`Scheme.exists_cappedDecoder`, from the locality of `W₁` at `Z`:
`θ (row_Z d) = min (W₁ d) (W₁ Z)`, exact by domination), the section `ρ ∘ V`, spliced with `⊥`
above `K`, is lawful at `K` (transport with `W₁` as lawful companion of the same bottom pattern,
`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`), equals `W₁` at every proper cell and every cell
`W₁` reads as `⊥`, and reads every other top `d` as `max (W₁ d) c`.

**The tie case from donor domination** (`StageType.lowStepTie_of_donorDomination`, compiled in this
repository).  If every capped lift of the donor from the root, literal on the root and agreeing
with the ambient donor face capped at the cap, can be chosen dominated at a top cell of graded index
`(univ, K)` (`StageType.DonorDomination`), the tie case `StageType.LowStepTie` holds: the raise
through the template keeps the root (proper root cells are kept, root tops are at least the
frontier already), keeps the capped agreement (the raised tops are at least the cap), and puts every
donor top off the root, at the tie or determined by the root included, at least at the frontier.
**The tie case through a top cell** (`StageType.lowStepTie_of_top`,
`StageType.lowStepTie_of_top_grade`, compiled in this repository).  Domination is not needed, nor
the top cell: the donor face at every LOW family (`StageType.IsLowFamily.exists_raised_of_gap`, in
`VaughtConjecture.Continuation.LowGapRaise`) raises the ambient donor face `R` at the frontier `c`
below the gap at the cap, through a top cell of the largest grade of a donor top
(`StageType.exists_raised_at_top`), agrees with `R` capped at the cap, and restores the root by
the capped lift at `c` from the root of the private face; it reads every top off the root at least
at `c`.  The tie case for every LOW family, donors whose tops all have grades below `K` included,
is `StageType.IsLowFamily.lowStepTie`, in `VaughtConjecture.Continuation.LowStepLow`.

**The unserved case at every grade** (`StageType.lowStepUnserved`, the full grade included, and
below the full grade `StageType.lowStepUnserved_of_le`, compiled in this repository): owner
lowering at the cap (`H2.exists_lowered_at_succ`: the face capped at the next label
self-visible at `K` above the cap carries its largest label at the owner, is capped below the
threshold, and the root is restored by a capped lift), with the context as its own donor.  With it
the capped lift into the LOW layer needs only the tie case
(`ProfileTower.Lvl.Good.cappedLift_lowS_of_tie`), and none of the named cases when the donor has a
top of grade `K` (`ProfileTower.Lvl.Good.cappedLift_lowS_of_top`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

/-! ### The raise through the template -/

namespace VaughtConjecture.StageType

open Finset Label H2

variable {α : Ordinal.{u}} {n K : ℕ}

/-- **The raise through the template.**  In a legal stage type `tb` on `n` points, let `Z` be a
cell labelled `⊤` of graded index `(univ, K)`, `0 < K ≤ n`, `W₁` lawful at `K` and dominated at
`Z` (`W₁ d ≤ W₁ Z` at every cell of grade at most `K`), and `c` self-visible at `K`.
Some `W` lawful at `K` equals `W₁` at every proper cell and every cell `W₁` reads as `⊥`, and
reads every other top `d` of grade at most `K` as `max (W₁ d) c`: the raise map of the capped
decoder of `W₁` at `Z` above the largest replaced reading of a proper cell, applied to the row of
`Z`. -/
theorem exists_raised_of_dominated {tb : StageType.{u} α n} (htb : tb.IsLegal) (hK0 : 0 < K)
    (hKn : K ≤ n) {Z : Fin tb.card} (hZ : tb.label Z = ⊤)
    (hZi : tb.toCellScheme.gradedIndex Z = (univ, K)) {W₁ : Fin tb.card → Label.{u}}
    (hW₁ : LawfulAt tb K W₁) (hdom : ∀ d, tb.toCellScheme.grade d ≤ K → W₁ d ≤ W₁ Z)
    {c : Label.{u}} (hc : IsSelfVisible K c) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → tb.label d ≠ ⊤ → W d = W₁ d) ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → W₁ d = ⊥ → W d = ⊥) ∧
      ∀ d, tb.toCellScheme.grade d ≤ K → tb.label d = ⊤ → W₁ d ≠ ⊥ → W d = max (W₁ d) c := by
  classical
  obtain ⟨W', hW', hW'W⟩ := exists_ext_bot_at htb hK0 hKn hW₁
  have hgZ : tb.toCellScheme.grade Z = K := congrArg Prod.snd hZi
  obtain ⟨θ, hθm, hθ0, -, hθc, hθb0, hθrow⟩ :=
    Scheme.exists_cappedDecoder (S := tb.toScheme) hW' hgZ
  have hbelow (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      d ∈ tb.toCellScheme.below (tb.toCellScheme.gradedIndex Z) := by
    rw [hZi]; exact ⟨subset_univ _, hd⟩
  have hθV (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      θ (tb.rowAt Z d) = W₁ d := by
    rw [hθrow d (hbelow d hd), hW'W d hd, hW'W Z hgZ.le]
    exact min_eq_left (hdom d hd)
  -- the threshold separating the tops from the proper cells in the template
  set Lo := univ.filter fun y ↦ tb.label y ≠ ⊤ ∧ tb.toCellScheme.grade y ≤ K with hLo
  set θb := Lo.sup fun y ↦ visibilityReplace K K (tb.rowAt Z y) with hθb_def
  have hθb : IsSelfVisible K θb := by
    refine Finset.sup_induction (p := IsSelfVisible K) (isSelfVisible_bot K) ?_ ?_
    · intro a ha b hb
      rcases max_choice a b with h1 | h1
      · rw [h1]; exact ha
      · rw [h1]; exact hb
    · intro y _
      exact visibilityReplace_self_visibilityReplace le_rfl _
  have hprop (y : Fin tb.card) (hy : tb.toCellScheme.grade y ≤ K) (hyt : tb.label y ≠ ⊤) :
      tb.rowAt Z y ≤ θb :=
    (le_visibilityReplace (by omega) _).trans
      (Finset.le_sup (f := fun y ↦ visibilityReplace K K (tb.rowAt Z y))
        (mem_filter.mpr ⟨mem_univ _, hyt, hy⟩))
  have htop (x : Fin tb.card) (hx : tb.toCellScheme.grade x ≤ K) (hxt : tb.label x = ⊤)
      (hx0 : tb.rowAt Z x ≠ ⊥) : θb < tb.rowAt Z x := by
    refine (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hx0)).mpr fun y hy ↦ ?_
    obtain ⟨-, hyt, hyK⟩ := mem_filter.mp hy
    have := visibilityReplace_rowAt_lt_of_top hZ (hbelow x hx) (hbelow y hyK) hxt hyt
    rwa [hgZ] at this
  have hρ : IsWitness (stepSuppressor K) (raiseMap θ θb c) :=
    isWitness_raiseMap hθm hθ0 hθc hθb0 hθb hc
  have hlawρ : tb.rows.IsLawfulBelow ((univ : Finset (Fin n)), K)
      (raiseMap θ θb c ∘ fun e ↦ tb.rowAt Z e.1) :=
    (Scheme.isLawfulBelow_rowAt htb.isConsistent hZi).map_of_bot_iff hW₁.1 (fun d ↦ d.2.2) hρ
      fun d ↦ by
        rw [raiseMap_eq_bot_iff, hθV d.1 d.2.2]
  set W : Fin tb.card → Label.{u} :=
    tb.toCellScheme.splice K (fun _ ↦ ⊥) fun d ↦ raiseMap θ θb c (tb.rowAt Z d) with hW
  have hWle (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      W d = raiseMap θ θb c (tb.rowAt Z d) :=
    CellScheme.splice_of_le hd
  refine ⟨W, ⟨(CellScheme.Rows.isLawfulBelow_congr (R := tb.rows)
      (X := ((univ : Finset (Fin n)), K)) (w := fun d ↦ raiseMap θ θb c (tb.rowAt Z d))
      (w' := W) fun d hd ↦
        (hWle d (show tb.toCellScheme.grade d ≤ K from hd.2)).symm).mp hlawρ,
      fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩,
    fun d hd hdt ↦ ?_, fun d hd h0 ↦ ?_, fun d hd hdt h0 ↦ ?_⟩
  · rw [hWle d hd]
    by_cases h0 : θ (tb.rowAt Z d) = ⊥
    · rw [raiseMap_of_bot h0, ← hθV d hd, h0]
    · rw [raiseMap_of_le h0 (hprop d hd hdt), hθV d hd]
  · rw [hWle d hd]
    exact raiseMap_of_bot (by rw [hθV d hd]; exact h0)
  · rw [hWle d hd]
    have hθ0' : θ (tb.rowAt Z d) ≠ ⊥ := by rw [hθV d hd]; exact h0
    have hV0 : tb.rowAt Z d ≠ ⊥ := fun h ↦ hθ0' (by rw [h, hθ0])
    rw [raiseMap_of_lt hθ0' (htop d hd hdt hV0), hθV d hd]

end VaughtConjecture.StageType

/-! ### The tie case from donor domination -/

namespace VaughtConjecture.StageType

open Finset Label H2 FieldAdmission

variable {α : Ordinal.{u}} {k : ℕ}

variable (K : ℕ) (t' tb : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
  (hp : restrictFace Fin.castSuccEmb t' = some p) (hpb : restrictFace Fin.castSuccEmb tb = some p)
  in
/-- **Donor domination** (open; the tie case is proved without it,
`StageType.IsLowFamily.lowStepTie`): for a private face `f` and a donor face `R` lawful at `K`
agreeing on the root capped at a cap `h` self-visible at `K`, some donor face lawful at `K`, literal
on the root and agreeing with `R` capped at `h`, is dominated at a cell of the donor labelled `⊤` of
graded index `(univ, K)`.  The donor-side counterpart of the domination by the owner. -/
def DonorDomination : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {R : Fin tb.card → Label.{u}}
    {f : Fin t'.card → Label.{u}}, LawfulAt tb K R → LawfulAt t' K f →
    (∀ x, min (f (faceCell hp x)) h = min (R (faceCell hpb x)) h) →
    ∃ (W₁ : Fin tb.card → Label.{u}) (Z : Fin tb.card), LawfulAt tb K W₁ ∧
      (∀ x, W₁ (faceCell hpb x) = f (faceCell hp x)) ∧ (∀ d, min (W₁ d) h = min (R d) h) ∧
      tb.label Z = ⊤ ∧ tb.toCellScheme.gradedIndex Z = (univ, K) ∧
      ∀ d, tb.toCellScheme.grade d ≤ K → W₁ d ≤ W₁ Z

variable {K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The tie case from donor domination.**  At a LOW family, donor domination gives the tie case
of the donor face, indeed the conclusion of `StageType.LowStepTie` without its tie premise: the
raise through the template (`StageType.exists_raised_of_dominated`) at the frontier `c` keeps the
proper cells, keeps the root tops (at least `c` by the strict source gaps,
`H2.frontier_le_lawfulAt`), keeps the capped agreement (the raised tops were at least the cap), and
reads every donor top off the root, at the tie or determined by the root included, at least at
`c`. -/
theorem lowStepTie_of_donorDomination (hF : IsLowFamily K t' tb p o r)
    (hD : DonorDomination K t' tb hF.face_private hF.face_donor) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r := by
  classical
  intro h c hh hb hhc R f hR hf hag hc htop _ _
  obtain ⟨W₁, Z, hW₁, hW₁r, hW₁R, hZ, hZi, hdom⟩ := hD hh hR hf hag
  have hs := hF.isSourceGapContextAt
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have hfo := frontier_le_lawfulAt hF.isLegal_private hs hf
  have hcv : IsSelfVisible K c := by
    rw [hc]
    rcases min_choice (f o) (visibilityReplace K K (f r)) with h1 | h1 <;> rw [h1]
    · exact hfo.1
    · exact visibilityReplace_self_visibilityReplace le_rfl _
  obtain ⟨W, hW, hWp, hW0, hWt⟩ :=
    exists_raised_of_dominated hF.isLegal_donor hK0 hKk hZ hZi hW₁ hdom hcv
  have hcb : ⊥ < c := hb.trans hhc
  -- the root tops of `W₁` are at least `c`
  have hroot_top (x : Fin p.card) (hx : tb.label (faceCell hF.face_donor x) = ⊤) :
      c ≤ W₁ (faceCell hF.face_donor x) := by
    rw [hW₁r, hc]
    refine hfo.2 _ ?_ (last_notMem_scope_faceCell hF.face_private x)
    rw [label_faceCell, ← label_faceCell hF.face_donor x]
    exact hx
  -- the tops of `W₁` of grade at most `K` are at least `h`
  have hWh (d : Fin tb.card) (hdK : tb.toCellScheme.grade d ≤ K) (hd : tb.label d = ⊤) :
      h ≤ W₁ d := by
    by_cases hv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨x, rfl⟩ := exists_faceCell_eq hF.face_donor hv
      exact hhc.le.trans (hroot_top x hd)
    · have h1 := hW₁R d
      rw [min_eq_right (htop d hd hdK hv)] at h1
      exact min_eq_right_iff.mp h1
  refine ⟨W, hW, fun x ↦ ?_, fun d ↦ ?_, fun d hd hdK hv ↦ ?_⟩
  · -- the root is literal
    set d := faceCell hF.face_donor x
    by_cases hdK : tb.toCellScheme.grade d ≤ K
    · by_cases hdt : tb.label d = ⊤
      · have hne : W₁ d ≠ ⊥ := ne_bot_of_gt (hcb.trans_le (hroot_top x hdt))
        rw [hWt d hdK hdt hne, max_eq_left (hroot_top x hdt), hW₁r]
      · rw [hWp d hdK hdt, hW₁r]
    · rw [hW.2 d hdK, ← hW₁r, hW₁.2 d hdK]
  · -- the capped agreement
    by_cases hdK : tb.toCellScheme.grade d ≤ K
    · by_cases hdt : tb.label d = ⊤
      · have hhd := hWh d hdK hdt
        have hne : W₁ d ≠ ⊥ := ne_bot_of_gt (hb.trans_le hhd)
        rw [hWt d hdK hdt hne, ← hW₁R d, min_eq_right hhd,
          min_eq_right (hhc.le.trans (le_max_right _ _))]
      · rw [hWp d hdK hdt]; exact hW₁R d
    · rw [hW.2 d hdK, hR.2 d hdK]
  · -- the donor tops off the root are at least `c`
    have hne : W₁ d ≠ ⊥ := ne_bot_of_gt (hb.trans_le (hWh d hdK hd))
    rw [hWt d hdK hd hne]
    exact le_max_right _ _

end VaughtConjecture.StageType

/-! ### The unserved case at every grade -/

namespace VaughtConjecture.StageType

open Finset Label H2 FieldAdmission

variable {α : Ordinal.{u}} {k K : ℕ}

/-- **The unserved case holds at every grade**: at a legal source-gap context `t'` of grade `K` on
`k + 1` points with the lost point last, with face `p` along the first points, the unserved case of
the private frontier (`StageType.LowStepUnserved`) holds, the full grade `K = k + 1` included: the
lowered face at the cap (`H2.exists_lowered_at_succ`, with the context as its own donor), where the
face is first capped at the next label self-visible at `K` above the cap so that the owner carries
its largest label, then capped below the threshold, and the root restored by a capped lift. -/
theorem lowStepUnserved {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p) :
    LowStepUnserved K t' (Fin.last k) o r := by
  intro u hu c hc hc0 hroot _ _ _
  have hs' : t'.IsSourceGapContextAt K ((Function.Embedding.refl (Fin k)).trans Fin.castSuccEmb)
      (Fin.last k) o r := by
    convert hs
    exact Function.Embedding.ext fun _ ↦ rfl
  set L : Fin t'.card → Label.{u} := t'.toCellScheme.splice K (fun _ ↦ ⊥) u with hL_def
  have hLle (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) : L d = u d :=
    CellScheme.splice_of_le hd
  have hL : LawfulAt t' K L :=
    ⟨(CellScheme.Rows.isLawfulBelow_congr (R := t'.rows) (X := ((univ : Finset (Fin (k + 1))), K))
      (w := u) (w' := L) fun d hd ↦
        (hLle d (show t'.toCellScheme.grade d ≤ K from hd.2)).symm).mp hu,
      fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩
  have hlow : ∀ x : Fin p.card, p.label x ≠ ⊤ → L (faceCell hp x) ≤ c := fun x hx ↦ by
    by_cases hd : t'.toCellScheme.grade (faceCell hp x) ≤ K
    · rw [hLle _ hd]
      exact hroot _ hd (last_notMem_scope_faceCell hp x) (by rwa [label_faceCell])
    · rw [hL_def, CellScheme.splice_of_lt (not_le.mp hd)]; exact bot_le
  obtain ⟨W, hW, hWr, hWL, hWf⟩ := exists_lowered_at_succ hleg hs' hp hleg hp hc hL hL
    (fun _ ↦ rfl) hc hc0 le_rfl hlow
  refine ⟨W, hW.1, fun d hd ↦ by rw [hWL d, hLle d hd], fun d hd hl ↦ ?_, hWf⟩
  obtain ⟨x, rfl⟩ := exists_faceCell_eq_of_last_notMem hp hl
  rw [hWr x, hLle _ hd]

/-- **The unserved case holds below the full grade** (`K ≤ k`): `StageType.lowStepUnserved`. -/
theorem lowStepUnserved_of_le {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r)
    (_hKk : K ≤ k) {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p) :
    LowStepUnserved K t' (Fin.last k) o r :=
  lowStepUnserved hleg hs hp

end VaughtConjecture.StageType

/-! ### The capped lift from the tie case alone -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {g : ℕ} {L : Lvl I g}

local notation "𝒞" => lowCat I (g + 1) N T o r

/-- **The capped lift from either coatom into the LOW layer over a good level, from the tie case
alone**: below the full grade the unserved case holds (`StageType.lowStepUnserved_of_le`), so
`ProfileTower.Lvl.Good.cappedLift_lowS_of_unserved_tie` needs only `StageType.LowStepTie`. -/
theorem Lvl.Good.cappedLift_lowS_of_tie (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1)
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
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_of_unserved_tie hgm hs htb
    (StageType.lowStepUnserved_of_le I.isLegal_left hs hgm I.restrictFace_face_left) hTie ho hr
    hNQ hTQ hNroot hTR hTtop hLoN hx

end VaughtConjecture.ProfileTower

/-! ### The tie case through a top cell -/

namespace VaughtConjecture.StageType

open Finset

variable {α : Ordinal.{u}} {K k : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
  {o r : Fin t'.card}

/-- **The tie case holds when the donor has a top cell of graded index `(univ, K)`** (for
instance a top of grade `K`, by availability): `StageType.IsLowFamily.exists_raised_of_gap`, which
uses neither the tie premise nor the top cell. -/
theorem lowStepTie_of_top (hF : IsLowFamily K t' tb p o r) {Z : Fin tb.card}
    (_hZ : tb.label Z = ⊤) (_hZi : tb.toCellScheme.gradedIndex Z = (univ, K)) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r :=
  fun _ hb hhc _ _ hR hf hag hc htop hlow _ ↦
    hF.exists_raised_of_gap hb hhc hR hf hag hlow hc htop

end VaughtConjecture.StageType

/-! ### The tie case through a top of the grade -/

namespace VaughtConjecture.StageType

variable {α : Ordinal.{u}} {k K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
  {o r : Fin t'.card}

/-- **The tie case when the donor has a top of grade `K`** (`StageType.lowStepTie_of_top` with the
top cell of `StageType.exists_top_cell_univ`): for instance when the donor has top grade `K`. -/
theorem lowStepTie_of_top_grade (hF : IsLowFamily K t' tb p o r) {x : Fin tb.card}
    (hx : tb.label x = ⊤) (hxK : tb.toCellScheme.grade x = K) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r := by
  obtain ⟨Z, hZ, hZi⟩ := exists_top_cell_univ hF.isLegal_donor hx
  exact lowStepTie_of_top hF hZ (hxK ▸ hZi)

end VaughtConjecture.StageType

/-! ### The capped lift when the donor has a top of the grade -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {g : ℕ} {L : Lvl I g}

local notation "𝒞" => lowCat I (g + 1) N T o r

/-- **The capped lift from either coatom into the LOW layer over a good level, when the donor has
a top of grade `g + 1`**: the tie case holds (`StageType.lowStepTie_of_top_grade`), so the capped
lift needs only the LOW designations. -/
theorem Lvl.Good.cappedLift_lowS_of_top (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {z : Fin I.right.card} (hz : I.right.label z = ⊤)
    (hzK : I.right.toCellScheme.grade z = g + 1)
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
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_of_tie hgm hs htb
    (StageType.lowStepTie_of_top_grade (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩) hz hzK) ho hr
    hNQ hTQ hNroot hTR hTtop hLoN hx

end VaughtConjecture.ProfileTower

/-! ### The LOW designations of a seed -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

open Classical in
/-- The **proper donor fields** of a seed at the grade `K`: the copies of the cells of the donor
(the right face) of grade at most `K` not labelled `⊤`. -/
noncomputable def lowN (K : ℕ) : Finset (Fin I.amalgam.card ⊕ Unit) :=
  (univ.filter fun t ↦ I.right.label t ≠ ⊤ ∧ I.right.toCellScheme.grade t ≤ K).image
    fun t ↦ Sum.inl (StageType.faceCell I.restrictFace_right t)

/-- The **donor tops** of a seed: the copies of the cells of the donor labelled `⊤`. -/
def lowT : Set (Fin I.amalgam.card ⊕ Unit) :=
  {f | ∃ t, I.right.label t = ⊤ ∧ f = Sum.inl (StageType.faceCell I.restrictFace_right t)}

variable {I}

/-- A copy of a donor cell of grade at most `K` lies below the donor coatom at `K`. -/
theorem faceCell_right_mem_below {K : ℕ} {t : Fin I.right.card}
    (ht : I.right.toCellScheme.grade t ≤ K) :
    StageType.faceCell I.restrictFace_right t ∈ I.amalgam.toCellScheme.below (coatD, K) := by
  rw [CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
    StageType.grade_faceCell]
  exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_right.le, ht⟩

/-- **The capped lift from either coatom into the LOW layer over a good level, for the LOW
designations of the seed**, when the private context is a source-gap context of grade `g + 1`
with the lost point last and the donor has top grade `g + 1`, attained: the designation hypotheses
of `ProfileTower.Lvl.Good.cappedLift_lowS_of_top` hold for `lowN`, `lowT` and the copies of the
owner and the lost top. -/
theorem Lvl.Good.cappedLift_lowS_seed {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {z : Fin I.right.card} (hz : I.right.label z = ⊤)
    (hzK : I.right.toCellScheme.grade z = g + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  refine hL.cappedLift_lowS_of_top hgm hs htb hz hzK rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  · rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  · intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  · exact fun f hf ↦ hf
  · exact fun t ht ↦ ⟨t, ht, rfl⟩
  · exact fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩

end VaughtConjecture.ProfileTower

/-! ### The tie case for donors with all tops below the grade -/

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

variable (K : ℕ) (t' tb : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
  (hp : restrictFace Fin.castSuccEmb t' = some p) (hpb : restrictFace Fin.castSuccEmb tb = some p)
  (o r : Fin t'.card) in
/-- **The tie case for a donor without a top of grade `K`** (proved at every LOW family,
`StageType.IsLowFamily.lowStepTieLow`, in `VaughtConjecture.Continuation.LowStepLow`): when no top
of the donor has
grade `K`, the tie case `StageType.LowStepTie`.  There is then no cell labelled `⊤` of graded index
`(univ, K)` in the donor to read through; the reading grade is the grade `K` of the owner of the
context, which the controllers must read, so it cannot be lowered to the top grade of the donor. -/
def LowStepTieLow : Prop :=
  (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≠ K) → LowStepTie K t' tb hp hpb o r

variable {K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The tie case from the case of a donor without a top of grade `K`**: with a top of grade `K`
it is `StageType.lowStepTie_of_top_grade`. -/
theorem lowStepTie_of_low (hF : IsLowFamily K t' tb p o r)
    (hlow : LowStepTieLow K t' tb hF.face_private hF.face_donor o r) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r := by
  by_cases h : ∃ x, tb.label x = ⊤ ∧ tb.toCellScheme.grade x = K
  · obtain ⟨x, hx, hxK⟩ := h
    exact lowStepTie_of_top_grade hF hx hxK
  · exact hlow fun x hx hxK ↦ h ⟨x, hx, hxK⟩

end VaughtConjecture.StageType

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The capped lift from either coatom into the LOW layer for the seed's designations, from the
case of a donor without a top of the grade** (`StageType.LowStepTieLow`); with a top of grade
`g + 1` no case is left (`ProfileTower.Lvl.Good.cappedLift_lowS_seed`). -/
theorem Lvl.Good.cappedLift_lowS_seed_of_low {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1)
    (hlow : StageType.LowStepTieLow (g + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r') {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  refine hL.cappedLift_lowS_of_tie hgm hs htb
    (StageType.lowStepTie_of_low (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩) hlow) rfl rfl
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  · rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  · intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  · exact fun f hf ↦ hf
  · exact fun t ht ↦ ⟨t, ht, rfl⟩
  · exact fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩

end VaughtConjecture.ProfileTower

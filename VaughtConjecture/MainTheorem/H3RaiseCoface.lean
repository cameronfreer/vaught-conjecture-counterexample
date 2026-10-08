/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Glue

/-!
# The donor raise over a gluing coface (work file for `h3`)

Work file (placement later), for the input (S2) of `VaughtConjecture.MainTheorem.H3Class`.
Compiled in this repository (theorem named):

* **A witness at the root** (`H3.RootWitness`, a named condition on a prescription): a witness
  `Φ`, bounded by a grade at least `n + 1` and sending no label of `d` other than `⊥` to `⊥`, with
  `θ ≤ Φ ⊤` and `Φ ∘ t.label` agreeing with the prescription on the root capped at `θ`.
* **A lift at the root** (`H3.RootLift`, a named condition on a prescription): a labelling lawful
  on `d` agreeing with the prescription on the root capped at `θ` and at least `θ` at the cells of
  `d` labelled `⊤`.  A witness image of `d.label` with a lawful companion of its zero set is one
  (`H3.rootLift_of_companion`), in particular a witness at the root (`H3.rootLift_of_rootWitness`).
* **The donor raise over a gluing coface from lifts at the root**
  (`H3.donorRaiseBotAtIn_of_rootLift`): the prescription on `p` (spliced at the grade), the lift of
  the root prescription to `d` relative to the lift at the root
  (`StageType.exists_isLawful_faceLift`), glued.
* **The donor raise over a gluing coface** (`H3.donorRaiseBotAtIn_of_gluesAt`): if the coface `tb`
  of `p` glues the lawful labellings of `p` and of `d` agreeing on the root
  (`StageType.GluesAt`), the donor raise in the class form holds at every grade from the grade of
  the cap at which every prescription has a witness at the root at a cap `θ` at least its marker
  value: the prescription on `p` (spliced at the grade), the base of the raise on `d`
  (`StageType.exists_isLawful_raise`), glued.
* **A gluing coface exists** (`H3.exists_gluingCoface`, from
  `StageType.exists_gluingPinnedExtension`).
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower StageType

namespace StageType

variable {α : Ordinal.{u}}

/-- **A labelling lawful below a graded face, read on the face, is lawful below its full scope
there.** -/
theorem isLawfulBelow_comp_faceCell {n m : ℕ} {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (h : restrictFace f D = some t) {x : Fin D.card → Label.{u}} {k : ℕ}
    (hx : D.rows.IsLawfulBelow ((univ : Finset (Fin m)).map f, k) fun z ↦ x z) :
    t.rows.IsLawfulBelow ((univ : Finset (Fin m)), k) fun i ↦ x (faceCell h i) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  exact (Scheme.isLawfulBelow_comap_cellMap_iff (S := D.toScheme) f
    ((univ : Finset (Fin m)), k) x).mpr hx

/-- **The base of the raise, at the cells labelled `⊤`.** -/
theorem exists_isLawful_raise_top {n : ℕ} {d : StageType.{u} α (n + 1)} (hd : d.IsLegal)
    {t : StageType.{u} α n} (ht : restrictFace Fin.castSuccEmb d = some t)
    {ψ : Fin t.card → Label.{u}} (hψ : t.rows.IsLawful ψ) {K : ℕ} (hK : n + 1 ≤ K)
    {Φ : Label.{u} → Label.{u}} (hΦ : IsWitness (stepSuppressor K) Φ)
    (hΦbot : ∀ z, Φ (d.label z) = ⊥ → d.label z = ⊥) {θ : Label.{u}}
    (hθ : IsSelfVisible (n + 1) θ) (hθΦ : θ ≤ Φ ⊤)
    (hroot : ∀ x, min (Φ (t.label x)) θ = min (ψ x) θ) :
    ∃ v : Fin d.card → Label.{u}, d.rows.IsLawful v ∧ (∀ x, v (faceCell ht x) = ψ x) ∧
      ∀ z, d.label z = ⊤ → θ ≤ v z := by
  obtain ⟨v, hv, hvψ, hvc⟩ := exists_isLawful_raise hd ht hψ hK hΦ hΦbot hθ hroot
  refine ⟨v, hv, hvψ, fun z hz ↦ ?_⟩
  have h := hvc z
  rw [hz, min_eq_right hθΦ] at h
  exact h ▸ min_le_left _ _

end StageType

namespace H3

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A witness at the root** for a prescription `ψ` on the root `t` of `d`, at the cap `θ`. -/
def RootWitness {d : StageType.{u} α (n + 1)} {t : StageType.{u} α n}
    (_ht : restrictFace Fin.castSuccEmb d = some t) (ψ : Fin t.card → Label.{u}) (θ : Label.{u}) :
    Prop :=
  ∃ K, n + 1 ≤ K ∧ ∃ Φ : Label.{u} → Label.{u}, IsWitness (stepSuppressor K) Φ ∧
    (∀ z, Φ (d.label z) = ⊥ → d.label z = ⊥) ∧ θ ≤ Φ ⊤ ∧
      ∀ x, min (Φ (t.label x)) θ = min (ψ x) θ

/-- **A lift at the root** for a prescription `ψ` on the root `t` of `d`, at the cap `θ`: a
labelling lawful on `d` agreeing with `ψ` on the root capped at `θ` and at least `θ` at the cells
of `d` labelled `⊤`. -/
def RootLift {d : StageType.{u} α (n + 1)} {t : StageType.{u} α n}
    (ht : restrictFace Fin.castSuccEmb d = some t) (ψ : Fin t.card → Label.{u}) (θ : Label.{u}) :
    Prop :=
  ∃ q : Fin d.card → Label.{u}, d.rows.IsLawful q ∧
    (∀ x, min (q (faceCell ht x)) θ = min (ψ x) θ) ∧ ∀ z, d.label z = ⊤ → θ ≤ q z

/-- **A witness image with a lawful companion is a lift at the root**: for a witness `Φ` bounded
by a grade at least `n + 1`, with `θ ≤ Φ ⊤`, agreeing with `ψ` on the root capped at `θ`, and some
lawful labelling of `d` that is `⊥` exactly where `Φ ∘ d.label` is `⊥`, the labelling
`Φ ∘ d.label` is lawful (`CellScheme.Rows.IsLawful.map_of_bot_iff`), so a lift at the root. -/
theorem rootLift_of_companion {d : StageType.{u} α (n + 1)} {t : StageType.{u} α n}
    (ht : restrictFace Fin.castSuccEmb d = some t) {ψ : Fin t.card → Label.{u}} {θ : Label.{u}}
    {K : ℕ} (hK : n + 1 ≤ K) {Φ : Label.{u} → Label.{u}} (hΦ : IsWitness (stepSuppressor K) Φ)
    {q₀ : Fin d.card → Label.{u}} (hq₀ : d.rows.IsLawful q₀)
    (hbot : ∀ z, Φ (d.label z) = ⊥ ↔ q₀ z = ⊥) (hθΦ : θ ≤ Φ ⊤)
    (hroot : ∀ x, min (Φ (t.label x)) θ = min (ψ x) θ) : RootLift ht ψ θ := by
  refine ⟨Φ ∘ d.label, d.isLawful.map_of_bot_iff hq₀ (fun z ↦ (d.grade_le z).trans hK) hΦ hbot,
    fun x ↦ ?_, fun z hz ↦ ?_⟩
  · change min (Φ (d.label (faceCell ht x))) θ = _
    rw [label_faceCell]
    exact hroot x
  · change θ ≤ Φ (d.label z)
    rw [hz]
    exact hθΦ

/-- **A witness at the root is a lift at the root** (`H3.rootLift_of_companion`, the companion
being `d.label`). -/
theorem rootLift_of_rootWitness {d : StageType.{u} α (n + 1)} {t : StageType.{u} α n}
    {ht : restrictFace Fin.castSuccEmb d = some t} {ψ : Fin t.card → Label.{u}} {θ : Label.{u}}
    (h : RootWitness ht ψ θ) : RootLift ht ψ θ := by
  obtain ⟨K, hK, Φ, hΦ, hΦbot, hθΦ, hroot⟩ := h
  exact rootLift_of_companion ht hK hΦ d.isLawful
    (fun z ↦ ⟨hΦbot z, fun h ↦ by rw [h, hΦ.map_bot]⟩) hθΦ hroot

section Raise

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {t : StageType.{u} α n} (hpt : restrictFace g p = some t)
  {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)
  (htbd : restrictFace (extendByLast g) tb = some d)

/-- The root cell of the amalgam of the seed at a cell of the root. -/
noncomputable def rootCell (x : Fin t.card) : Fin (seed ht' hp htb).amalgam.card :=
  faceCell (restrictFace_left_seed ht' hp htb) (faceCell hp (faceCell hpt x))

/-- **The donor raise over a gluing coface, from lifts at the root.**  If `tb` glues the lawful
labellings of `p` and of `d` agreeing on the root, then at a grade `N ≤ k' ≤ k + 1` the donor
raise in the class form holds as soon as every prescription not `⊥` at the cap and in the class
has, on the root, a lift at a cap `θ` self-visible at `n + 1` and at least its marker value
(`H3.RootLift`). -/
theorem donorRaiseBotAtIn_of_rootLift {c r : Fin t'.card} (hc : 0 < t'.toCellScheme.grade c)
    (hglue : GluesAt htb.2 htbd hpt hd.2) {k' : ℕ}
    (hn : n < k') (hk' : k' ≤ k + 1) (B : Set (Fin (seed ht' hp htb).amalgam.card))
    (hwit : ∀ f : ProfileTower.Prof (seed ht' hp htb),
      (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k')
        (fun e ↦ f e) →
      f (requests ht' hp htb htbd c r hc).cap ≠ ⊥ →
      (∀ e ∈ B, e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
        (univ.erase (Fin.last (k + 1)), k') → f e ≠ ⊥) →
      ∃ θ : Label.{u}, IsSelfVisible (n + 1) θ ∧
        (requests ht' hp htb htbd c r hc).markerValue f ≤ θ ∧
        RootLift hd.2 (fun x ↦ f (rootCell ht' hp htb hpt x)) θ) :
    CapRequests.DonorRaiseBotAtIn (requests ht' hp htb htbd c r hc) B (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) k' := by
  classical
  intro f hf _ hcap hcl
  have hL := restrictFace_left_seed ht' hp htb
  have hR : restrictFace (Coatom.right k) (seed ht' hp htb).amalgam = some tb :=
    (seed ht' hp htb).restrictFace_right
  set pc : Fin p.card → Fin (seed ht' hp htb).amalgam.card := fun i ↦ faceCell hL (faceCell hp i)
  have hpcR (i : Fin p.card) : pc i = faceCell hR (faceCell htb.2 i) :=
    faceCell_faceCell (h := Fin.castSuccEmb) hL hR hp htb.2 i
  -- the prescription on `p`, spliced at `k'`
  have hft' : t'.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), k')
      fun x ↦ f (faceCell hL x) := by
    refine isLawfulBelow_comp_faceCell hL ?_
    rw [Coatom.univ_map_left]
    exact hf
  have hfp : p.rows.IsLawfulBelow ((univ : Finset (Fin k)), k') fun i ↦ f (pc i) := by
    have h := (isLawfulBelow_comp_faceCell hp (x := fun x ↦ f (faceCell hL x)) (k := k'))
    exact h ((Rows.isLawfulBelow_congr (w := fun x ↦ f (faceCell hL x))
      (w' := fun x ↦ f (faceCell hL x)) fun _ _ ↦ rfl).mp (by
        have := hft'.mono (X := ((univ : Finset (Fin k)).map Fin.castSuccEmb, k'))
          (Prod.mk_le_mk.mpr ⟨subset_univ _, le_rfl⟩)
        exact this))
  set wP : Fin p.card → Label.{u} :=
    p.toCellScheme.splice k' (fun _ ↦ ⊥) fun i ↦ f (pc i) with hwPdef
  have hwP : p.rows.IsLawful wP := Scheme.isLawful_splice_bot (S := p.toScheme) hfp
  have hwPle (i : Fin p.card) (hi : p.toCellScheme.grade i ≤ k') : wP i = f (pc i) :=
    CellScheme.splice_of_le hi
  -- the root prescription
  set ψ : Fin t.card → Label.{u} := fun x ↦ wP (faceCell hpt x)
  have hψ : t.rows.IsLawful ψ := isLawful_comp_faceCell hpt hwP
  have hψf (x : Fin t.card) : ψ x = f (rootCell ht' hp htb hpt x) := by
    refine hwPle _ ?_
    rw [grade_faceCell]
    exact (t.grade_le x).trans hn.le
  obtain ⟨θ, hθ, hmθ, q, hq, hqroot, hqtop⟩ := hwit f hf hcap hcl
  obtain ⟨vd, hvd, hvdψ, hvdc⟩ := exists_isLawful_faceLift hd.1 hd.2 hψ hq hθ
    fun x ↦ by rw [hψf]; exact hqroot x
  have hvdtop (z : Fin d.card) (hz : d.label z = ⊤) : θ ≤ vd z := by
    have h := hvdc z
    rw [min_eq_right (hqtop z hz)] at h
    exact h ▸ min_le_left _ _
  obtain ⟨w, hw, hwP', hwd⟩ := hglue wP hwP vd hvd fun i ↦ (hvdψ i).symm
  refine ⟨faceExtend hR w, ?_, fun e he heD ↦ ?_, fun y hy ↦ ?_⟩
  · have h := isLawfulBelow_of_faceCell hR (x := faceExtend hR w)
      (by simpa only [faceExtend_faceCell] using hw)
    rw [Coatom.univ_map_right] at h
    exact h.mono (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩)
  · -- a cell of the common face
    obtain ⟨y, rfl⟩ := exists_faceCell_eq hR (i := e) (Scheme.mem_visibleCells.mpr fun z hz ↦ by
      have h := heD.1 hz
      rw [← Coatom.univ_map_right] at h
      obtain ⟨w', -, hw'⟩ := mem_map.mp h
      exact ⟨w', hw'⟩)
    have hlast : Fin.last k ∉ tb.toCellScheme.scope y := by
      intro hm
      have hmem : Fin.last (k + 1) ∈
          (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hR y) := by
        rw [scope_faceCell]
        exact mem_map.mpr ⟨Fin.last k, hm, by simp [Coatom.right]⟩
      exact (mem_erase.mp (he.1 hmem)).1 rfl
    obtain ⟨i, rfl⟩ := exists_faceCell_eq_of_last_notMem htb.2 hlast
    rw [faceExtend_faceCell, hwP', ← hpcR]
    refine hwPle i ?_
    have h := he.2
    change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hR (faceCell htb.2 i)) ≤ k' at h
    rwa [grade_faceCell, grade_faceCell] at h
  · -- a new top of the donor
    obtain ⟨j, hj, -, rfl⟩ := hy
    have hA := restrictFace_donor_seed ht' hp htb htbd
    rw [faceCell_trans (extendByLast_trans g Fin.castSuccEmb) hR htbd hA j, faceExtend_faceCell,
      hwd]
    exact hmθ.trans (hvdtop j hj)

/-- **The donor raise over a gluing coface.**  If `tb` glues the lawful labellings of `p` and of
`d` agreeing on the root, then at a grade `N ≤ k' ≤ k + 1` the donor raise in the class form holds
as soon as every prescription not `⊥` at the cap and in the class has, on the root, a witness at
a cap `θ` self-visible at `n + 1` and at least its marker value (`H3.donorRaiseBotAtIn_of_rootLift`,
`H3.rootLift_of_rootWitness`). -/
theorem donorRaiseBotAtIn_of_gluesAt {c r : Fin t'.card} (hc : 0 < t'.toCellScheme.grade c)
    (hglue : GluesAt htb.2 htbd hpt hd.2) {k' : ℕ}
    (hn : n < k') (hk' : k' ≤ k + 1) (B : Set (Fin (seed ht' hp htb).amalgam.card))
    (hwit : ∀ f : ProfileTower.Prof (seed ht' hp htb),
      (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k')
        (fun e ↦ f e) →
      f (requests ht' hp htb htbd c r hc).cap ≠ ⊥ →
      (∀ e ∈ B, e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
        (univ.erase (Fin.last (k + 1)), k') → f e ≠ ⊥) →
      ∃ θ : Label.{u}, IsSelfVisible (n + 1) θ ∧
        (requests ht' hp htb htbd c r hc).markerValue f ≤ θ ∧
        RootWitness hd.2 (fun x ↦ f (rootCell ht' hp htb hpt x)) θ) :
    CapRequests.DonorRaiseBotAtIn (requests ht' hp htb htbd c r hc) B (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) k' :=
  donorRaiseBotAtIn_of_rootLift ht' hp htb hpt hd htbd hc hglue hn hk' B fun f hf hcap hcl ↦ by
    obtain ⟨θ, hθ, hm, hw⟩ := hwit f hf hcap hcl
    exact ⟨θ, hθ, hm, rootLift_of_rootWitness hw⟩

end Raise

/-- **A gluing coface exists**: at a limit stage, for a legal `t'` with face `p` along the first
points and face `t` along `g.trans Fin.castSuccEmb`, every coface `d` of `t` is the face along
`extendByLast g` of a coface `tb` of `p` that glues the lawful labellings of `p` and of `d` agreeing
on `t` (`StageType.exists_gluingPinnedExtension`). -/
theorem exists_gluingCoface (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    (ht' : t'.IsLegal) {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n} (hpt : restrictFace g p = some t)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      GluesAt htb.2 htbd hpt hd.2 := by
  obtain ⟨Q, hQ, h₁, h₂, hgl⟩ := exists_gluingPinnedExtension hα.isSuccPrelimit
    (ht'.restrictFace _ hp) hpt hd.1 hd.2
  exact ⟨Q, ⟨hQ, h₁⟩, h₂, hgl⟩

end H3

end VaughtConjecture

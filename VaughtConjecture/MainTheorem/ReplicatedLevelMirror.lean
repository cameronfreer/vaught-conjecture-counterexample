/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelInstances
import VaughtConjecture.Extension.AttachmentMirror

/-!
# The copies of a re-rendered level

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**Lifts into a full face pass to the mirroring** (`Scheme.cappedLift_mirror_of`): for any scheme
`T`, a family `𝒰` of faces other than the ground set no member of which lies inside the scope of
a cell of proper scope, and a pair `X` whose face contains no member of `𝒰`, a capped lift of `T`
from `X` into a pair of full scope is a capped lift of its mirroring (`Scheme.mirror`: the cells of
`T` followed by their copies at the faces of `𝒰`, every cell reading the row of its original).
The ambient read on `T` is lawful (`Scheme.isLawfulBelow_castAdd_mirror`); the lift of `T` read
through the originals is lawful (the mirroring is saturated), reads the prescription (below `X`
every cell is a cell of `T`), and keeps the observation of the ambient (a copy carries the label
of its original).

**The replicated level** (`Seed.ALvl.Good.rep`): a good level mirrored at the mixed faces of the
seed.  It is well formed when the level has the faces of the amalgam, which every level has
(`Seed.faces_lvLevel`), and consistent (`Seed.ALvl.Good.isConsistent_rep`).  Its section
(`Seed.ALvl.Good.repσ`, a copy carrying the section of its original) is lawful below `(univ, j)` at
the lawful admitted states, takes values in the code grid at `j + 1`, is readable at a canonical
state, and keeps capped agreement, the copied cells included.  It lifts from the context coatom
wherever the level does (`Seed.ALvl.Good.cappedLift_rep`).

**At the apex input** (`ApexInstance.lvRep_cappedLift_three`), for the requests with the cap at
the apex (threshold `3`, the top grade), the replicated level at every grade `j + 1 ≤ 3` is well
formed, consistent, and lifts capped from the context coatom into `(univ, j + 1)`.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType AvailableTopDeterminationCounterexample

namespace Scheme

variable {n : ℕ} {T : Scheme.{u} n} {𝒰 : Finset (Finset (Fin n))}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ 𝒰, ¬ U ⊆ T.toCellScheme.scope c}

/-- **Sections of `T` from sections of its mirroring**: a labelling of the mirroring lawful below a
pair, read on the cells of `T`, is lawful below that pair (a copy has a scope in `𝒰`, neither the
ground set nor inside the scope of a cell of proper scope). -/
theorem isLawfulBelow_castAdd_mirror (h𝒰 : ∀ U ∈ 𝒰, U ≠ univ) {Y : Finset (Fin n) × ℕ}
    {w : Fin (T.card + T.copyCount 𝒰) → Label.{u}}
    (hw : (mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) :
    T.rows.IsLawfulBelow Y fun x ↦ w (Fin.castAdd _ x) := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hmem (x : Fin T.card) (Z : Finset (Fin n) × ℕ) :
      (Fin.castAdd _ x : Fin (T.card + T.copyCount 𝒰)) ∈ (mirror hmix).toCellScheme.below Z ↔
        x ∈ T.toCellScheme.below Z := by
    rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_mirror_castAdd (hmix := hmix)]
  have hgr (x : Fin T.card) :
      (mirror hmix).toCellScheme.grade (Fin.castAdd _ x) = T.toCellScheme.grade x :=
    congrArg Prod.snd (gradedIndex_mirror_castAdd (hmix := hmix) x)
  have hsc (x : Fin T.card) :
      (mirror hmix).toCellScheme.scope (Fin.castAdd _ x) = T.toCellScheme.scope x :=
    congrArg Prod.fst (gradedIndex_mirror_castAdd (hmix := hmix) x)
  refine (CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun x ↦ w (Fin.castAdd _ x))).mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
    fun s t ht hst hg ↦ ?_⟩
  · rw [← hgr]
    exact ho _ ((hmem d Y).mpr hd)
  · have hφ (d : T.toCellScheme.below (T.toCellScheme.gradedIndex s)) :
        (Fin.castAdd _ d.1 : Fin (T.card + T.copyCount 𝒰)) ∈
          (mirror hmix).toCellScheme.below
            ((mirror hmix).toCellScheme.gradedIndex (Fin.castAdd _ s)) := by
      rw [gradedIndex_mirror_castAdd (hmix := hmix)]
      exact (hmem _ _).mpr d.2
    have h := (hl _ ((hmem s Y).mpr hs)).reindex
      fun d : T.toCellScheme.below (T.toCellScheme.gradedIndex s) ↦
        (⟨Fin.castAdd _ d.1, hφ d⟩ : (mirror hmix).toCellScheme.below
          ((mirror hmix).toCellScheme.gradedIndex (Fin.castAdd _ s)))
    convert h using 1
    · funext d
      exact (hgr d.1).symm
    · funext d
      change T.rows.row s d = (mirror hmix).rows.row (Fin.castAdd _ s) ⟨Fin.castAdd _ d.1, hφ d⟩
      rw [← Scheme.rowAt_of_mem d.2, ← Scheme.rowAt_of_mem (hφ d), Scheme.rowAt_mirror_castAdd]
    · rfl
  · obtain ⟨u', hu', hle⟩ := ha (Fin.castAdd _ s) (Fin.castAdd _ t) ((hmem t Y).mpr ht)
      (by rw [hsc, hsc]; exact hst) (by rw [hgr, hgr]; exact hg)
    induction u' using Fin.addCases with
    | left x =>
      refine ⟨x, ?_, hle⟩
      rw [← gradedIndex_mirror_castAdd (hmix := hmix), hu',
        gradedIndex_mirror_castAdd (hmix := hmix)]
    | right j =>
      exfalso
      have hj : (mirror hmix).toCellScheme.scope (Fin.natAdd _ j) = T.toCellScheme.scope t :=
        (congrArg Prod.fst hu').trans (hsc t)
      have hm : (mirror hmix).toCellScheme.scope (Fin.natAdd _ j) ∈ 𝒰 := by
        rw [scope_mirror_natAdd]; exact ((T.copyEquiv 𝒰).symm j).2.1
      by_cases htu : T.toCellScheme.scope t = univ
      · exact h𝒰 _ hm (hj.trans htu)
      · exact hmix t htu _ hm (le_of_eq hj)

/-- **Lifts into a full face pass to the mirroring**, from a pair whose face contains no member of
`𝒰`. -/
theorem cappedLift_mirror_of (h𝒰 : ∀ U ∈ 𝒰, U ≠ univ) {X Y : Finset (Fin n) × ℕ} (h : X ≤ Y)
    (hY : Y.1 = univ) (hX : ∀ U ∈ 𝒰, ¬ U ⊆ X.1) (hT : T.rows.CappedLift h) :
    (mirror hmix).rows.CappedLift h := by
  refine CellScheme.Rows.cappedLift_of_forall_full h fun c hc w v hw hv hwv ↦ ?_
  obtain ⟨q, hq, hqc, hqw⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists h).mp hT c hc
    (fun x ↦ w (Fin.castAdd _ x.1)) (fun x ↦ v (Fin.castAdd _ x.1))
    (isLawfulBelow_castAdd_mirror h𝒰 hw) (isLawfulBelow_castAdd_mirror h𝒰 hv) fun d ↦
      hwv _ (by rw [CellScheme.mem_below, gradedIndex_mirror_castAdd (hmix := hmix)]; exact d.2)
  set r : Fin T.card → Label.{u} := CellScheme.Rows.extendBot Y q with hr
  have hrl : T.rows.IsLawfulBelow Y fun x ↦ r x :=
    CellScheme.Rows.isLawfulBelow_extendBot.mpr hq
  have horig (t : Fin (T.card + T.copyCount 𝒰)) (ht : t ∈ (mirror hmix).toCellScheme.below Y) :
      T.mirrorOrig 𝒰 t ∈ T.toCellScheme.below Y :=
    ⟨hY ▸ subset_univ _, ht.2⟩
  refine ⟨fun t ↦ r (T.mirrorOrig 𝒰 t),
    (mirrorData hmix).isLawfulBelow_comp hrl horig (saturated_mirrorData _ Y),
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · -- the observation of the ambient
    have hcY : (Fin.castAdd _ (T.mirrorOrig 𝒰 t) : Fin (T.card + T.copyCount 𝒰)) ∈
        (mirror hmix).toCellScheme.below Y := by
      rw [CellScheme.mem_below, gradedIndex_mirror_castAdd (hmix := hmix)]; exact horig t ht
    have hvt : v t = v (Fin.castAdd _ (T.mirrorOrig 𝒰 t)) :=
      eq_of_mirrorOrig_eq hv (mirrorOrig_castAdd _ _ _).symm
        (((mirrorData hmix).scope_subset t).trans
          (le_of_eq (congrArg Prod.fst (gradedIndex_mirror_castAdd (hmix := hmix) _)).symm)) hcY
    beta_reduce
    rw [hvt, hr, CellScheme.Rows.extendBot_of_mem q (horig t ht)]
    exact hqc ⟨_, horig t ht⟩
  · -- the prescription below `X`
    induction t using Fin.addCases with
    | right j =>
      exfalso
      have hm : (mirror hmix).toCellScheme.scope (Fin.natAdd _ j) ∈ 𝒰 := by
        rw [scope_mirror_natAdd]; exact ((T.copyEquiv 𝒰).symm j).2.1
      exact hX _ hm ht.1
    | left x =>
      have hx : x ∈ T.toCellScheme.below X := by
        rw [CellScheme.mem_below, ← gradedIndex_mirror_castAdd (hmix := hmix)]
        exact ht
      beta_reduce
      rw [mirrorOrig_castAdd, hr, CellScheme.Rows.extendBot_of_mem q (CellScheme.below_mono _ h hx)]
      exact hqw ⟨_, hx⟩

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B j : ℕ}
  {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} {N : I.ALvl g H j}

/-- A mixed face is a proper face whose points are neither all context points nor all donor
points. -/
theorem ne_univ_of_mem_mixedFaces {U : Finset (Fin (m + 2))} (hU : U ∈ I.mixedFaces g) :
    U ≠ univ :=
  ((I.mem_mixedFaces g).mp hU).2.1

/-- No mixed face lies inside the context coatom. -/
theorem not_subset_ctxCoatom_of_mem_mixedFaces {U : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) : ¬ U ⊆ univ.erase (Fin.last (m + 1)) := by
  rw [← Coatom.univ_map_left]
  exact ((I.mem_mixedFaces g).mp hU).2.2.1

namespace ALvl.Good

/-- **No mixed face lies inside the scope of a cell of proper scope** of a good level: such a cell
is a cell of the attachment, whose scope lies in the context face or the donor face. -/
theorem not_subset_scope (hN : N.Good B A) (z : Fin N.S.card)
    (hz : N.S.toCellScheme.scope z ≠ univ) (U : Finset (Fin (m + 2)))
    (hU : U ∈ I.mixedFaces g) : ¬ U ⊆ N.S.toCellScheme.scope z := by
  obtain ⟨d, rfl⟩ := hN.mem_range z hz
  rw [hN.scope_attEmb]
  obtain ⟨-, -, hc, hdn⟩ := (I.mem_mixedFaces g).mp hU
  intro hUd
  rcases I.scope_attachment g d with h | h
  · exact hc (hUd.trans h)
  · exact hdn (hUd.trans h)

/-- **The replicated level**: a good level with a copy of each cell of full scope at each mixed
face of size at least its grade, every copy reading the row of its original. -/
noncomputable abbrev rep (hN : N.Good B A) : Scheme.{u} (m + 2) :=
  Scheme.mirror hN.not_subset_scope

/-- **The replicated level is consistent.** -/
theorem isConsistent_rep (hN : N.Good B A) : hN.rep.rows.IsConsistent :=
  Scheme.isConsistent_mirror hN.consistent

/-- **The replicated level is well formed** when the level has the faces of the amalgam. -/
theorem isWellFormed_rep (hN : N.Good B A)
    (hf : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces) : hN.rep.IsWellFormed :=
  Scheme.isWellFormed_mirror hN.wf fun _ hU ↦ hf ▸ ((I.mem_mixedFaces g).mp hU).1

/-- **The section of the replicated level**: a copy carries the section of its original. -/
noncomputable def repσ (_hN : N.Good B A) (P : Fin (I.attachment g).card → Label.{u})
    (t : Fin (N.S.card + N.S.copyCount (I.mixedFaces g))) : Label.{u} :=
  N.σ P (N.S.mirrorOrig (I.mixedFaces g) t)

/-- **The section of the replicated level is lawful below `(univ, j)`** at the lawful admitted
states with values self-visible at `1`, the copied cells included. -/
theorem isLawfulBelow_repσ (hN : N.Good B A) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) (fun d ↦ P d))
    (hv : ∀ e, IsSelfVisible 1 (P e)) (hA : A j P) :
    hN.rep.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun t ↦ hN.repσ P t :=
  (Scheme.mirrorData hN.not_subset_scope).isLawfulBelow_comp (hN.lawful P hP hv hA)
    (fun _ ht ↦ ⟨subset_univ _, ht.2⟩) (Scheme.saturated_mirrorData _ _)

/-- **The copied cells are short and readable**: the section of the replicated level takes values
in the code grid at `j + 1`, and at a canonical state in that grid it is readable at `j + 1`. -/
theorem repσ_mem_codeGrid (hN : N.Good B A) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : ∀ d, P d ∈ codeGrid (j + 1) B)
    (hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P d))
    (t : Fin (N.S.card + N.S.copyCount (I.mixedFaces g))) :
    hN.repσ P t ∈ codeGrid (j + 1) B :=
  hN.mem P hP hP1 _

theorem isReadableAt_repσ (hN : N.Good B A) {Q : Fin (I.attachment g).card → Label.{u}}
    (hQ : orbitCode (j + 1) Q = Q) (hQB : ∀ d, Q d ∈ codeGrid (j + 1) B)
    (hQ1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ Q d))
    (t : Fin (N.S.card + N.S.copyCount (I.mixedFaces g))) :
    IsReadableAt (j + 1) Q (hN.repσ Q t) :=
  hN.readable Q hQ hQB hQ1 _

/-- **The section of the replicated level keeps capped agreement**, the copied cells included. -/
theorem min_repσ_eq (hN : N.Good B A) {P P' : Fin (I.attachment g).card → Label.{u}}
    (hP : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P d))
    (hP' : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P' d))
    (hPB : ∀ d, P d ∈ codeGrid (j + 1) B) {h : Label.{u}} (hh : IsSelfVisible (j + 1) h)
    (hs : IsShort (j + 1) h) (hag : ∀ d, min (P d) h = min (P' d) h)
    (t : Fin (N.S.card + N.S.copyCount (I.mixedFaces g))) :
    min (hN.repσ P t) h = min (hN.repσ P' t) h :=
  hN.capAgree P P' hP hP' hPB h hh hs hag _

/-- **The replicated level lifts from the context coatom** into a pair of full scope wherever the
level does: the copies have mixed scope, never inside the context coatom. -/
theorem cappedLift_rep (hN : N.Good B A) {X Y : Finset (Fin (m + 2)) × ℕ} (h : X ≤ Y)
    (hY : Y.1 = univ) (hX : X.1 ⊆ univ.erase (Fin.last (m + 1)))
    (hT : N.S.rows.CappedLift h) : hN.rep.rows.CappedLift h :=
  Scheme.cappedLift_mirror_of (fun _ hU ↦ ne_univ_of_mem_mixedFaces hU) h hY
    (fun _ hU hsub ↦ not_subset_ctxCoatom_of_mem_mixedFaces hU (hsub.trans hX)) hT

end ALvl.Good

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **Every level has the faces of the amalgam.** -/
theorem faces_lvLevel : ∀ j,
    (I.lvLevel g H B hd Q j).S.toCellScheme.faces = I.amalgam.toCellScheme.faces
  | 0 => rfl
  | j + 1 => faces_lvLevel j

end Seed

end VaughtConjecture

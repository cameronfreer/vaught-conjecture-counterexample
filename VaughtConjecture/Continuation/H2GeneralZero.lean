/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralBelow

/-!
# h2 at every arity: the engine on one point (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**The completion from the grade `N ≤ 1` on every seed** (`H2.exists_rowCompletion₀_of_le_one`):
`Seed.exists_rowCompletion₀` asks `0 < m` only for the canonical lifts below the grade `N`; from
`N ≤ 1` every lift is one of the predicate, so seeds on two points are allowed.

**The engine on one point** (`H2.admittedCompletionsAt_zero`): a context on one point has top grade
`1`, its full grade; the engine below the full grade (`H2.exists_completion_below_of_le_one`) needs
no extension above `1` (there is no grade above it on one point).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission ProfileTower CellScheme

/-- **The completion on the catalogues of a predicate from a grade `N ≤ 1`**, for every seed
(`Seed.exists_rowCompletion₀` without `0 < m`). -/
theorem exists_rowCompletion₀_of_le_one {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    {N : ℕ} (hN : N ≤ 1) {Rw : I.State → Prop}
    (hbotP : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionOf Rw k x)
    (hcapP : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      CapLiftProvisionOf Rw k x)
    (hdown : ∀ k, N ≤ k → ∀ R ∈ rowCat Rw (k + 1), code k R ∈ rowCat Rw k)
    (hlab : N ≤ m + 1 → Rw (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows N Rw := by
  classical
  set D := rowFamily I N Rw
  have hD (k : ℕ) : D k ⊆ cat I k := rowCat_subset _ k
  have hdD := rowFamily_down (fun k hk _ ↦ hdown k hk)
  have hdD' (k : ℕ) (hk : k + 1 ≤ m) := hdD k (by omega)
  have hprov (k : ℕ) (hk0 : 0 < k) (hkm : k ≤ m + 1) (x : Fin (m + 2))
      (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
      BotLiftProvisionIn (rowFamily I N Rw k) k x ∧
        CapLiftProvisionIn (rowFamily I N Rw k) k x := by
    rw [rowFamily_of_le _ (by omega)]
    exact ⟨hbotP k (by omega) hkm x hx, hcapP k (by omega) hkm x hx⟩
  have hL := lvlOn₀_goodOn hD hdD' (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).1)
    (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).2) m le_rfl
  have hR := lvlOn₀_rowsInAll hD hdD' (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).1)
    (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).2) m le_rfl
  set Rt : I.State → Prop := fun s ↦ N ≤ m + 1 → Rw s
  have hdtop : ∀ R ∈ rowCat Rt (m + 1), code m R ∈ D m := hdD m le_rfl
  have hbot (x) (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
      BotLiftProvisionOf Rt (m + 1) x := (hprov _ (by omega) le_rfl x hx).1
  have hcap (x) (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
      CapLiftProvisionOf Rt (m + 1) x := (hprov _ (by omega) le_rfl x hx).2
  have hlab' : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ rowCat Rt (m + 1) := by
    have hW : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    exact mem_rowCat.mpr ⟨code_mem_cat_of_isCutLawful hW, hlab⟩
  set L := lvlOn₀ I D m
  refine ⟨hL.admittedTopCompletion Rt hdtop hbot hcap hlab', fun u k hu hk ↦ ?_⟩
  -- The rows of the completion: the top layer, then the layers of the levels.
  change Rw fun d ↦ (L.nextSOn (rowCat Rt (m + 1))).rowAt u
    (L.embedOn (rowCat Rt (m + 1)) d)
  induction u using Fin.addCases with
  | right i =>
    obtain ⟨R, hR', hrow⟩ := hL.rowAt_nextSOn (C := rowCat Rt (m + 1))
      (u := Fin.natAdd _ i) (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)
    have hki : k = m + 1 := by
      have := congrArg Prod.snd hu
      change ((L.S.appendFullCellsScheme (m + 1) (rowCat Rt (m + 1)).card).gradedIndex
        (Fin.natAdd _ i)).2 = _ at this
      rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at this
      exact this.symm
    rw [funext hrow]
    exact (mem_rowCat.mp hR').2 (hki ▸ hk)
  | left e =>
    have he : L.S.toCellScheme.gradedIndex e = ((univ : Finset (Fin (m + 2))), k) :=
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).symm.trans hu
    obtain ⟨R, hR', hrow⟩ := hR e k he
    have hrow' (d : Fin I.amalgam.card) :
        (L.nextSOn (rowCat Rt (m + 1))).rowAt (Fin.castAdd _ e)
          (L.embedOn (rowCat Rt (m + 1)) d) = hat I k R d :=
      (Scheme.rowAt_appendFullCells_castAdd
        (r' := fun i ↦ L.ΦOn (rowCat Rt (m + 1)) (entryOn (rowCat Rt (m + 1)) i))
        (h := L.not_le) e (L.embed d)).trans (hrow d)
    rw [funext hrow']
    have hR'' : R ∈ rowCat Rw k := by
      have := hR'
      simp only [D, rowFamily_of_le Rw hk] at this
      exact this
    exact (mem_rowCat.mp hR'').2

variable {α : Ordinal.{u}}

/-- **The completion with the clause on the rows from a grade `K ≤ 1`**, for every seed. -/
theorem exists_completion_below_of_le_one {m : ℕ} {I : Seed.{u} α m} {K : ℕ}
    {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}
    (hS : IsStateAdmission (rootLm I) (rootRm I) K (LawfulAt I.left K) (LawfulAt I.right K) Adm)
    (hK1 : K ≤ 1) (hKm : K ≤ m + 1) (hextL : ExtAbove I.left I.restrictFace_face_left K)
    (hextR : ExtAbove I.right I.restrictFace_face_right K) (hreads : ReadsAt I K Adm)
    (hst : Adm I.left.label I.right.label) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows K (rowAdm I K Adm) := by
  refine exists_rowCompletion₀_of_le_one I hK1
    (fun j hj hjm x hx ↦ (liftProvisions_below hS hextL hextR hj hjm hx).1)
    (fun j hj hjm x hx ↦ (liftProvisions_below hS hextL hextR hj hjm hx).2)
    (fun j hj R hR ↦ ?_) (fun _ ↦ ?_)
  · obtain ⟨hRcat, hRA⟩ := mem_rowCat.mp hR
    have hRA' : rowAdm I K Adm R := by
      unfold rowAdm at hRA ⊢; rwa [trK_hat (by omega)] at hRA
    have hc := (mem_cat.mp hRcat).1
    exact code_mem_rowCat_below hS hj ⟨hc.1.mono (X := (_, j)) ⟨subset_rfl, by omega⟩,
      hc.2.mono (X := (_, j)) ⟨subset_rfl, by omega⟩⟩ hRA'
  · have hcut : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    have hA : rowAdm I K Adm fun d ↦ I.amalgam.label d := by
      unfold rowAdm stateAdm
      refine hreads (fun z hz ↦ ?_) (fun z hz ↦ ?_) hst
      · rw [trK_ctx, ite_eq_left hz]
        exact (StageType.label_faceCell _ z).symm
      · rw [trK_don, ite_eq_left hz]
        exact (StageType.label_faceCell _ z).symm
    exact (mem_rowCat.mp (code_mem_rowCat_below hS hKm hcut hA)).2

/-- On one point there is no grade above `1`: the extension above `1` holds vacuously. -/
theorem extAbove_one_point {t : StageType.{u} α 1} {p : StageType.{u} α 0}
    (hp : restrictFace Fin.castSuccEmb t = some p) : ExtAbove t hp 1 :=
  fun _ h1 h2 ↦ absurd h2 (by omega)

/-- **The engine on one point** (the input `H2.AdmittedCompletionsAt` at `k = 0`). -/
theorem admittedCompletionsAt_zero : AdmittedCompletionsAt.{u} 0 := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops _ hTops hS
  set Lo1 : Finset (Fin tb.card) := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K with hLo1
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hK1 : K ≤ 1 := hs.grade_owner ▸ t'.grade_le o
  obtain rfl : K = 1 := by omega
  have hr : t'.toCellScheme.grade r ≤ 1 := by
    have := grade_le_topGrade hs.label_lost
    rwa [hs.topGrade_eq] at this
  have hreads : ReadsAt (Seed.ofCoatoms hleg htbleg hp htbp) 1 (SelfLowG o r 1 Lo1 Tops) :=
    fun _ _ _ _ hL hR h ↦ selfLow_reads hs.grade_owner.le hr (fun t ht ↦ (hTops t ht).2.1)
      hL hR h
  have hst : SelfLowG o r 1 Lo1 Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  obtain ⟨F, hF⟩ := exists_completion_below_of_le_one
    (I := Seed.ofCoatoms hleg htbleg hp htbp) hS le_rfl le_rfl (extAbove_one_point hp)
    (extAbove_one_point htbp) hreads hst
  have hsub : Lo1 ⊆ Lo := fun x hx ↦ (mem_filter.mp hx).1
  exact ⟨F, fun q hq hqo ↦ selfLow_of_subset hsub
    (adm_of_hasAdmittedRows_below hS hreads hK0 le_rfl hF hs.grade_owner hq hqo)⟩

/-- **h2 with the lost point last at every arity from owner lowering below the designated tops and
the extension above `K`** (the engines on one and two points compiled). -/
theorem coatomCutoffDeterminationLast_of_ownerLowering_ext
    (hOL : ∀ k, OwnerLoweringBelowAt.{u} k) (hext : ∀ k, 2 ≤ k → ExtAboveAt.{u} k) :
    CoatomCutoffDeterminationLast.{u} :=
  coatomCutoffDeterminationLast_of_ext hOL admittedCompletionsAt_zero hext

end VaughtConjecture.H2

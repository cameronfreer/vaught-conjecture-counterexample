/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Witness

/-!
# Strict inequalities under transformations (work file for `h3`)

Work file (placement later), for a tightened admission at a cap below the top grade.  A class
condition `s x < s w` is closed backward under a transformation `d ↦ min (σ (s d)) (g (grade d))`
when `grade x ≤ grade w` (the suppressor is antitone), and not otherwise.  Compiled in this
repository (theorem named):

* **Backward closure** (`Label.lt_of_transform_lt`): for a witness `(g, σ)` and
  `grade x ≤ grade w`, `min (σ a) (g (grade x)) < min (σ b) (g (grade w))` gives `a < b`.
* **Its failure in the other direction** (`Label.not_lt_of_transform_lt_step`): with the step
  suppressor at `1` and the identity, a cell of grade `2` read `1` and a cell of grade `1` read `1`
  are transformed to `⊥ < 1`, while `¬ 1 < 1`.  The same splice is the downward clause of the
  engine (`ProfileTower.hat` at a grade below the cell).  So the strict inequalities `s a < s y`
  for a cell `a` of the common face of grade at least `N` and a top `y` of grade below `N` are not
  closed backward under the witnesses the engine uses.
* **The strict class at the grade of the cap** (`CapRequests.InStrictClass`,
  `CapRequests.AdmitsStrict`, `H3.strictCells`): the bottom class with, in addition, every cell of
  the common face of the grade `N` of the cap not labelled `⊤` strictly below every top.  It is
  closed backward under the witnesses with suppressor `⊤` at the grades of those cells
  (`CapRequests.InStrictClass.of_transform`, `CapRequests.AdmitsStrict.map_top`,
  `CapRequests.AdmitsStrict.comp`), so under the splices and codes at the grades `≥ N`: the downward
  clause of the engine holds (`CapRequests.code_mem_rowCat_strict_of_mem_rowCat`).
* **Recognition at a cell labelled `⊤`** (`CompletionBelowFullGrade.adm_of_isLawfulBelow_top`) needs
  only those witnesses, and **determination** follows from rows admitted in the strict class
  (`H3.isDeterminedWithin_of_strictRows`): a member literal on `t'` reads a strict cell at its label
  in `t'`, below the cutoff, and every top at least the cutoff.
-/

universe u

namespace VaughtConjecture

namespace Label

/-- **Strict inequalities are closed backward under a transformation when the first cell has the
smaller grade.** -/
theorem lt_of_transform_lt {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    {a b : Label.{u}} {i j : ℕ} (hij : i ≤ j) (h : min (σ a) (g i) < min (σ b) (g j)) : a < b := by
  by_contra hab
  rw [not_lt] at hab
  exact absurd h (not_lt.mpr (min_le_min (hw.monotone hab) (hw.antitone hij)))

/-- **Strict inequalities are not closed backward when the first cell has the larger grade**: the
step suppressor at `1` with the identity sends a value `1` at a grade `2` to `⊥` and a value `1` at
the grade `1` to `1`. -/
theorem not_lt_of_transform_lt_step :
    min (id (1 : Label.{u})) (stepSuppressor.{u} 1 2) <
        min (id (1 : Label.{u})) (stepSuppressor.{u} 1 1) ∧
      IsWitness (stepSuppressor.{u} 1) id ∧ ¬ (1 : Label.{u}) < 1 := by
  refine ⟨?_, IsWitness.id_step 1, lt_irrefl _⟩
  rw [stepSuppressor_of_lt (by norm_num), stepSuppressor_of_le le_rfl, min_bot_right,
    min_top_right]
  exact WithBot.bot_lt_coe _

end Label

open Finset Label

namespace CapRequests

section Strict

variable {ι : Type*} (r : CapRequests ι) (B A : Set ι)

/-- **The strict class**: no cell of `B` is `⊥`, and every cell of `A` reads strictly below every
cell of `T`. -/
def InStrictClass (s : ι → Label.{u}) : Prop :=
  (∀ d ∈ B, s d ≠ ⊥) ∧ ∀ a ∈ A, ∀ y ∈ r.T, s a < s y

/-- **Admission in the strict class**: correct as soon as in the strict class. -/
def AdmitsStrict (s : ι → Label.{u}) : Prop := r.InStrictClass B A s → r.IsCorrect s

variable {r B A} {s : ι → Label.{u}}

/-- **The strict class is closed backward under a transformation whose suppressor is `⊤` at the
grades of the cells of `A` and `T`.** -/
theorem InStrictClass.of_transform {grade : ι → ℕ} {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (hg : ∀ d, d ∈ A ∨ d ∈ r.T → g (grade d) = ⊤)
    (h : r.InStrictClass B A fun d ↦ min (σ (s d)) (g (grade d))) : r.InStrictClass B A s := by
  refine ⟨fun d hd hb ↦ h.1 d hd (by
    change min (σ (s d)) (g (grade d)) = ⊥
    rw [hb, hw.map_bot, min_bot_left]), fun a ha y hy ↦ ?_⟩
  have h' : min (σ (s a)) (g (grade a)) < min (σ (s y)) (g (grade y)) := h.2 a ha y hy
  rw [hg a (.inl ha), hg y (.inr hy), min_top_right, min_top_right] at h'
  by_contra hle
  exact absurd h' (not_lt.mpr (hw.monotone (not_lt.mp hle)))

/-- **Transformations with suppressor `⊤` at the grades of `A` and `T` keep admission in the strict
class.** -/
theorem AdmitsStrict.map_top (hs : r.AdmitsStrict B A s) {grade : ι → ℕ} (hgr : r.IsGraded grade)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (hg : ∀ d, d ∈ A ∨ d ∈ r.T → g (grade d) = ⊤) :
    r.AdmitsStrict B A fun d ↦ min (σ (s d)) (g (grade d)) := fun hcl ↦
  (hs (hcl.of_transform hw hg)).map hgr hw

/-- **Plain images keep admission in the strict class**, for a witness bounded by a grade at least
the threshold. -/
theorem AdmitsStrict.comp (hs : r.AdmitsStrict B A s) {K : ℕ} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness (stepSuppressor K) σ) (hNK : r.N ≤ K) (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) :
    r.AdmitsStrict B A (σ ∘ s) := fun hcl ↦ by
  refine (hs ⟨fun d hd hb ↦ hcl.1 d hd (by
    change σ (s d) = ⊥
    rw [hb, hw.map_bot]), fun a ha y hy ↦ ?_⟩).comp hw hNK hoff
  have h' : σ (s a) < σ (s y) := hcl.2 a ha y hy
  by_contra hle
  exact absurd h' (not_lt.mpr (hw.monotone (not_lt.mp hle)))

end Strict

open ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {B A : Set (Fin I.amalgam.card)}

/-- The splice at a grade at least those of `A` and `T` keeps admission in the strict class. -/
theorem AdmitsStrict.hat {P : Prof I} (hs : r.AdmitsStrict B A P)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hk : ∀ d, d ∈ A ∨ d ∈ r.T → I.amalgam.toCellScheme.grade d ≤ k) :
    r.AdmitsStrict B A (hat I k P) := by
  rw [hat_eq_min]
  exact hs.map_top hgr (IsWitness.id_step k) fun d hd ↦ stepSuppressor_of_le (hk d hd)

/-- The code at a grade at least the threshold and those of `A` and `T` keeps admission in the
strict class. -/
theorem AdmitsStrict.code {P : Prof I} (hs : r.AdmitsStrict B A P)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ} (hNk : r.N ≤ k)
    (hk : ∀ d, d ∈ A ∨ d ∈ r.T → I.amalgam.toCellScheme.grade d ≤ k) :
    r.AdmitsStrict B A (code k P) :=
  (hs.hat hgr hk).comp (isWitness_orbitMap k (ProfileTower.hat I k P)) hNk hgr.off_le

/-- **The downward clause for the catalogues of states admitted in the strict class**, at a grade
at least the threshold and those of `A` and `T`. -/
theorem code_mem_rowCat_strict_of_mem_rowCat (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hNk : r.N ≤ k) (hk : ∀ d, d ∈ A ∨ d ∈ r.T → I.amalgam.toCellScheme.grade d ≤ k)
    {R : Prof I} (hR : R ∈ rowCat (r.AdmitsStrict B A) (k + 1)) :
    code k R ∈ rowCat (r.AdmitsStrict B A) k := by
  obtain ⟨hRc, hRr⟩ := mem_rowCat.mp hR
  refine mem_rowCat.mpr ⟨code_mem_cat_of_mem_cat hRc, ?_⟩
  have h := (hRr.code hgr hNk hk).hat hgr hk
  rwa [code, hat_hat_succ] at h

end CapRequests

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {F : CompletionBelowFullGrade I} {N : ℕ}
  {Adm : I.State → Prop}

/-- **Recognition at a cell labelled `⊤`**: as `CompletionBelowFullGrade.adm_of_isLawfulBelow`,
for `q` lawful below `(univ, j)` that is `⊤` at the cell `u` of graded index `(univ, j)`, from the
closure of `Adm` only under the witnesses whose suppressor is `⊤` at `j`. -/
theorem adm_of_isLawfulBelow_top {j : ℕ}
    (hmap : ∀ (s : I.State) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), Adm s →
      IsWitness g σ → g j = ⊤ → Adm fun d ↦ min (σ (s d)) (g (I.amalgam.toCellScheme.grade d)))
    (hF : F.HasAdmittedRows N Adm) (hj : N ≤ j) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun z ↦ q z)
    {u : Fin F.scheme.card} (hu : F.scheme.toCellScheme.gradedIndex u = (univ, j))
    (hqu : q u = ⊤) : Adm (ProfileTower.hat I j (fun e ↦ q (F.embed e))) := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have hub : u ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) :=
    F.scheme.toCellScheme.mem_below_gradedIndex u
  obtain ⟨g, σ, hw, heq⟩ := hloc u (by rw [CellScheme.mem_below, hu])
  have hgu : F.scheme.toCellScheme.grade u = j := congrArg Prod.snd hu
  have hgj : g j = ⊤ := by
    have h := heq ⟨u, by rw [CellScheme.mem_below, hu]⟩
    change min (q u) (q u) = min _ (g (F.scheme.toCellScheme.grade u)) at h
    rw [hqu, min_self, hgu] at h
    exact (min_eq_top.mp h.symm).2
  convert hmap _ g σ (hF hu hj) hw hgj using 1
  funext d
  have hgi := F.gradedIndex_embed d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
  · have hmem : F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact ⟨subset_univ _, hd⟩
    rw [ProfileTower.hat_of_le hd, rowState, Scheme.rowAt_of_mem hmem,
      ← F.isLowerEmbedding.grade_eq d]
    have h := heq ⟨F.embed d, hmem⟩
    change min (q (F.embed d)) (q u) = _ at h
    rw [hqu, min_top_right] at h
    exact h
  · have hmem : F.embed d ∉ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
      rw [CellScheme.mem_below, hgi, hu]
      exact fun h ↦ hd h.2
    rw [ProfileTower.hat_of_lt (not_le.mp hd), rowState, Scheme.rowAt_of_notMem hmem, hw.map_bot,
      min_bot_left]

end CompletionBelowFullGrade

namespace H3

open StageType Label

variable {α : Ordinal.{u}} {n k : ℕ}

section Strict

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **The strict cells**: the cells of the common face of the grade of the cap whose label is not
`⊤`. -/
def strictCells (c : Fin t'.card) : Set (Fin (seed ht' hp htb).amalgam.card) :=
  {e | ∃ x : Fin p.card, p.toCellScheme.grade x = t'.toCellScheme.grade c ∧ p.label x ≠ ⊤ ∧
    e = faceCell (restrictFace_left_seed ht' hp htb) (faceCell hp x)}

/-- **Determination from a completion with rows admitted in the strict class.** -/
theorem isDeterminedWithin_of_strictRows (hα : Order.IsSuccLimit α)
    (hd : restrictFace (extendByLast g) tb = some d) {c r : Fin t'.card}
    (hc : t'.IsTopCap c) (hr : t'.IsMarker c r) (hn : n + 1 < t'.toCellScheme.grade c)
    (F : CompletionBelowFullGrade (seed ht' hp htb))
    (hF : F.HasAdmittedRows (t'.toCellScheme.grade c)
      ((requests ht' hp htb hd c r (by omega)).AdmitsStrict (classCells ht' hp htb hd)
        (strictCells ht' hp htb c))) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily (F.completion hα.isSuccPrelimit) δ) t'
        (g.trans Fin.castSuccEmb) d := by
  have hα' := hα.isSuccPrelimit
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hr.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hmap : ∀ (s : (seed ht' hp htb).State) (g' : ℕ → Label.{u}) (σ' : Label.{u} → Label.{u}),
      (requests ht' hp htb hd c r (by omega)).AdmitsStrict (classCells ht' hp htb hd)
        (strictCells ht' hp htb c) s → IsWitness g' σ' → g' (t'.toCellScheme.grade c) = ⊤ →
      (requests ht' hp htb hd c r (by omega)).AdmitsStrict (classCells ht' hp htb hd)
        (strictCells ht' hp htb c)
        fun d ↦ min (σ' (s d)) (g' ((seed ht' hp htb).amalgam.toCellScheme.grade d)) :=
    fun s g' σ' hs hw hgN ↦ hs.map_top hgr hw fun e he ↦ top_le_iff.mp (hgN ▸ hw.antitone (by
      rcases he with ⟨x, hx, -, rfl⟩ | he
      · rw [grade_faceCell, grade_faceCell, hx]
      · exact (hgr.grade_le_of_mem_T e he).trans_eq
          (grade_faceCell (restrictFace_left_seed ht' hp htb) c)))
  have h₁ : restrictFace Fin.castSuccEmb (F.completion hα') = some t' :=
    F.restrictFace_left_completion hα'
  have hR : restrictFace (extendByLast Fin.castSuccEmb) (F.completion hα') = some tb :=
    F.restrictFace_right_completion hα'
  have h₂ : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') =
      some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hnk : n ≤ k := by simpa using Fintype.card_le_of_embedding g
  have hf₂ : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ univ := fun he ↦ by
    have := congrArg Finset.card he
    rw [card_map, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at this
    omega
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα (F.completion hα')
  refine ⟨δ, hδ, (isDeterminedWithin_receivingFamily_iff h₂ hδD).mpr ?_⟩
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁ i j hij hj
  obtain ⟨hS, hqδ⟩ := hq
  change S = (F.completion hα').toScheme at hS
  subst hS
  obtain rfl : i = faceCell h₂ j := Fin.ext hij
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  by_cases hjl : Fin.last n ∈ d.toCellScheme.scope j
  · -- a new top: recognition at a cell of `(univ, N)` labelled `⊤`
    have hcap : ℓ (faceCell h₁ c) = ⊤ := (hold c).trans hc.2.1
    have hmark : ℓ (faceCell h₁ r) = ⊤ := (hold r).trans hr.1
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL c] at hcap
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL r] at hmark
    have hcg : (F.completion hα').toCellScheme.grade (faceCell h₁ c) = t'.toCellScheme.grade c :=
      grade_faceCell h₁ c
    have hN0 : 0 < t'.toCellScheme.grade c := by omega
    have hNk : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
    obtain ⟨u₀, hu₀⟩ := (F.isLegal_completion hα').isComplete
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
      ⟨(F.completion hα').univ_mem_faces, hN0, by simp; omega⟩
    obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
      (by rw [show (F.completion hα').toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
          exact subset_univ _)
      (hcg.trans (congrArg Prod.snd hu₀).symm)
    have hℓu : ℓ u = ⊤ := by
      have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
      rw [hold, hc.2.1] at h'
      exact top_le_iff.mp h'
    obtain ⟨w, rfl, hw'⟩ := F.exists_castSucc_of_gradedIndex_completion hα' (by omega)
      (hu.trans hu₀)
    -- the labelling read on the scheme below the full grade
    have hq' := (F.isLawful_comp_castSucc_completion hα' hl).isLawfulBelow
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
    have hrec := CompletionBelowFullGrade.adm_of_isLawfulBelow_top hmap hF le_rfl
      (q := fun z ↦ ℓ (Fin.castSucc z)) hq' hw' hℓu
    have hcl : ∀ e ∈ classCells ht' hp htb hd, ProfileTower.hat (seed ht' hp htb)
        (t'.toCellScheme.grade c) (fun e ↦ ℓ (Fin.castSucc (F.embed e))) e ≠ ⊥ := by
      intro e he
      rw [ProfileTower.hat_of_le (grade_lt_of_mem_classCells ht' hp htb hd hn he).le]
      rcases he with ⟨x, -, hx, rfl⟩ | ⟨j', hj', -, rfl⟩
      · intro hbot
        apply hx
        rw [← hold x, F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL x]
        exact hbot
      · intro hbot
        replace hbot : ℓ (faceCell h₂ j') = ⊥ := by
          rw [F.faceCell_completion hα' hf₂ h₂ hA j']
          exact hbot
        have h' := hqδ ⟨(faceCell h₂ j' : ℕ), (faceCell h₂ j').2⟩ (faceCell h₂ j') rfl
        change min (ℓ (faceCell h₂ j')) δ = _ at h'
        rw [hbot, min_bot_left, label_faceCell h₂ j', hj', min_top_left] at h'
        exact hδ.1.ne h'
    have hst : ∀ a ∈ strictCells ht' hp htb c, ∀ y ∈ (requests ht' hp htb hd c r (by omega)).T,
        ProfileTower.hat (seed ht' hp htb) (t'.toCellScheme.grade c)
          (fun e ↦ ℓ (Fin.castSucc (F.embed e))) a <
        ProfileTower.hat (seed ht' hp htb) (t'.toCellScheme.grade c)
          (fun e ↦ ℓ (Fin.castSucc (F.embed e))) y := by
      rintro a ⟨x, hxg, hxt, rfl⟩ y ⟨j', hj', hjl', rfl⟩
      have hag : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL (faceCell hp x)) ≤
          t'.toCellScheme.grade c := by rw [grade_faceCell, grade_faceCell, hxg]
      have hyg : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hA j') ≤
          t'.toCellScheme.grade c := (grade_lt_of_mem_classCells ht' hp htb hd hn
            (.inr ⟨j', hj', hjl', rfl⟩)).le
      rw [ProfileTower.hat_of_le hag, ProfileTower.hat_of_le hyg]
      have hval : ℓ (Fin.castSucc (F.embed (faceCell hL (faceCell hp x)))) = p.label x := by
        have h0 := hold (faceCell hp x)
        rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL, label_faceCell] at h0
        exact h0
      have hδa : (F.completion hα').label (faceCell h₁ (faceCell hp x)) < δ :=
        hδD _ (by rw [label_faceCell, label_faceCell]; exact hxt)
      rw [label_faceCell, label_faceCell] at hδa
      have hy : δ ≤ ℓ (faceCell h₂ j') := by
        have h' := hqδ ⟨(faceCell h₂ j' : ℕ), (faceCell h₂ j').2⟩ (faceCell h₂ j') rfl
        change min (ℓ (faceCell h₂ j')) δ = _ at h'
        rw [label_faceCell h₂ j', hj', min_top_left] at h'
        exact h' ▸ min_le_left _ _
      rw [F.faceCell_completion hα' hf₂ h₂ hA j'] at hy
      rw [hval]
      exact hδa.trans_le hy
    replace hrec := hrec ⟨hcl, hst⟩
    have hcapN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL c).le
    have hmarkN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL r) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL r).trans_le hrc
    have hyT : faceCell hA j ∈ (requests ht' hp htb hd c r (by omega)).T := ⟨j, hj, hjl, rfl⟩
    have htop := hrec.eq_top_of_mem_T hyT
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL c) = ⊤
          rw [ProfileTower.hat_of_le hcapN]; exact hcap)
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL r) = ⊤
          rw [ProfileTower.hat_of_le hmarkN]; exact hmark)
    have hyN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hA j) ≤
        t'.toCellScheme.grade c := by
      rw [grade_faceCell]
      exact (d.grade_le j).trans hn.le
    rw [ProfileTower.hat_of_le hyN] at htop
    change ℓ (faceCell h₂ j) = ⊤
    rw [F.faceCell_completion hα' hf₂ h₂ hA j]
    exact htop
  · -- an old cell: visible through the first points, literal on `t'`
    have hvis : faceCell h₂ j ∈ (F.completion hα').visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro y hy
      rw [scope_faceCell] at hy
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      induction x using Fin.lastCases with
      | last => exact absurd hx hjl
      | cast x => exact ⟨Fin.castSucc (g x), by simp⟩
    obtain ⟨z, hz⟩ := exists_faceCell_eq h₁ hvis
    change ℓ (faceCell h₂ j) = ⊤
    rw [← hz, hold]
    have h1 := label_faceCell h₁ z
    have h2 := label_faceCell h₂ j
    rw [hz] at h1
    rw [← h1, h2]
    exact hj



end Strict

end H3

end VaughtConjecture

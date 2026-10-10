/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftExtension

/-!
# The ambient's admission: recognition below the full face

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

Let `q` be lawful below the full face `(univ, j)` of the replicated scheme, at a grade `j` at
least the threshold `N` of the requests.  **The state of `q` on the attachment is admitted**
(`Seed.ambientAdmitted`): if it is in the exact class with a positive cap value, the cap cell
(grade `N`) has, by availability, a controller `u` of full scope at the grade `N` carrying at least
its label; `u` is the cell of a catalogue state `R`, admitted by the catalogue predicate.  The
capped decoder `θ` of `q` at `u` (`Scheme.exists_cappedDecoder_below`) reads the row of `u` as `q`
capped at `q u`: `θ (R c) = min (q c) (q u)` at every cell `c` of the attachment of grade at most
`N` (`Seed.exists_controller_decoder`).  The top rung of the member of `R` is read by `u` above
every value of `R`, so it is positive, hence every rung is (`Scheme.rungs_ne_bot_of_top`); every
positive value of `R` is read at a rung, so `θ` sends no positive value of `R` to `⊥`.  So `R` has
the exact class of `q`, reads the requests, and `θ` carries the reads to `q` capped at `q u`
(`StageType.GrowthRequests.CorrectAt.map`), which at least the cap value changes no read
(`StageType.GrowthRequests.CorrectAt.of_min`).

This is the recognition of the ladder controllers (`GrowthCarrier.recognizes_of_ladder`) at the
level of the sections of the replicated scheme below the full face, at the original controllers
(the copies are not needed: the cap cell has full scope in the context, and the controllers have
full scope).  The proof follows the copy recognition (`Seed.copy_recognition`) and the positivity of
the top rung (`Seed.exists_copiedTopRung_ne_bot`) at the original cells.

With it, the context lift needs only the extension over the tower
(`Seed.hasContextLift_attachAdmits_tower`).

## References

The controllers of the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The controller above a cell of the attachment, with its decoder.**  For `q` lawful below
`(univ, j)` and a cell `x` of the attachment of grade `N`, `2 ≤ N ≤ j`, `N ≤ m + 1`, with `q`
positive at `x`: some cell `u` of full scope at the grade `N` carries at least the label of `x`;
it is the cell of a lawful catalogue state `R` at the grade `N`; and some witness `θ` bounded by
`N`, bounded by `q u`, reads `R` as `q` capped at `q u` at the cells of grade at most `N`, and
sends no positive value of `R` to `⊥`. -/
theorem exists_controller_decoder (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j N : ℕ}
    (hN2 : 2 ≤ N) (hNj : N ≤ j) (hNm : N ≤ m + 1)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ q d)
    {x : Fin (I.attachment g).card} (hxN : (I.attachment g).toCellScheme.grade x = N)
    (hx0 : q (I.attachEmb g H Γ A B' x) ≠ ⊥) :
    ∃ u : Fin (I.replicated g H Γ A B').card,
      u ∈ (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ∧
      (I.replicated g H Γ A B').toCellScheme.grade u = N ∧
      q (I.attachEmb g H Γ A B' x) ≤ q u ∧
      ∃ R ∈ (I.attachmentBase g).towerCat Γ A N, (I.attachment g).rows.IsLawful R ∧
        ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor N) θ ∧
          (∀ c, (I.attachment g).toCellScheme.grade c ≤ N →
            θ (R c) = min (q (I.attachEmb g H Γ A B' c)) (q u)) ∧
          ∀ y, R y ≠ ⊥ → θ (R y) ≠ ⊥ := by
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  -- a cell of full scope at the grade `N`
  obtain ⟨f, hf⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') hH hne m N
    (by omega) (by omega)
  have hfE : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ f) =
      ((univ : Finset (Fin (m + 2))), N) := (Scheme.gradedIndex_mirror_castAdd _).trans hf
  have hfY : (Fin.castAdd _ f : Fin (I.replicated g H Γ A B').card) ∈
      (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hfE]
    exact ⟨subset_rfl, hNj⟩
  have hxg : (I.replicated g H Γ A B').toCellScheme.grade (I.attachEmb g H Γ A B' x) = N :=
    (congrArg Prod.snd (gradedIndex_attachEmb x)).trans hxN
  -- availability above `x`
  obtain ⟨u', hu', hxu⟩ := havail (I.attachEmb g H Γ A B' x) _ hfY
    (subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst hfE).symm))
    (hxg.trans (congrArg Prod.snd hfE).symm)
  have hu'E : (I.replicated g H Γ A B').toCellScheme.gradedIndex u' =
      ((univ : Finset (Fin (m + 2))), N) := hu'.trans hfE
  have hu'Y : u' ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) := CellScheme.Rows.mem_below_of_le (le_of_eq hu') hfY
  obtain ⟨u, rfl⟩ : ∃ u : Fin (I.attachTower g H Γ A B').card, u' = Fin.castAdd _ u := by
    induction u' using Fin.addCases with
    | left u => exact ⟨u, rfl⟩
    | right jj =>
      exfalso
      exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd jj)).2.1 (congrArg Prod.fst hu'E)
  have hu : (I.attachTower g H Γ A B').toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), N - 2 + 2) := by
    rw [show N - 2 + 2 = N by omega]
    exact (Scheme.gradedIndex_mirror_castAdd u).symm.trans hu'E
  obtain ⟨R, hRC, hR, hrowA, hrowL⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard (N - 2) m (by omega) u hu
  obtain ⟨-, htop, hval⟩ := Scheme.LadderBaseData.ladderController_clauses hH hcard hR
  set a := Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR with ha
  -- the capped decoder at `u`
  obtain ⟨θ, hθ, -, hθrow⟩ := Scheme.exists_cappedDecoder_below hq hu'Y
    (congrArg Prod.snd hu'E)
  have hugE : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u) =
      ((univ : Finset (Fin (m + 2))), N) := hu'E
  -- the reading of the attachment
  have hreadA (c : Fin (I.attachment g).card) (hc : (I.attachment g).toCellScheme.grade c ≤ N) :
      θ (R c) = min (q (I.attachEmb g H Γ A B' c)) (q (Fin.castAdd _ u)) := by
    have hcm : I.attachEmb g H Γ A B' c ∈ (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
      rw [CellScheme.mem_below, hugE, gradedIndex_attachEmb]
      exact ⟨subset_univ _, hc⟩
    have hrc : (I.replicated g H Γ A B').rowAt (Fin.castAdd _ u) (I.attachEmb g H Γ A B' c) =
        R c :=
      (Scheme.rowAt_mirror_castAdd _ _).trans
        (hrowA c (show (I.attachment g).toCellScheme.grade c ≤ N - 2 + 2 by omega))
    rw [← hrc]
    exact hθrow _ hcm
  -- the rungs of the member of `R`
  let p : ℕ → Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H := fun i ↦
    (a, Sum.inl ⟨min i (H - 1), by omega⟩)
  have hself (i : ℕ) (hi : i < H) :
      Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H) a
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H (p i))) = i + 1 := by
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H) (p i)
    simp only [p, Scheme.ladderCeil, Sum.elim_inl] at h
    rw [h]
    omega
  let r : ℕ → Fin (I.replicated g H Γ A B').card := fun i ↦ Fin.castAdd _ (ladCell H Γ A B' (p i))
  have hrg (i : ℕ) : (I.replicated g H Γ A B').toCellScheme.gradedIndex (r i) =
      ((univ : Finset (Fin (m + 2))), 1) :=
    (Scheme.gradedIndex_mirror_castAdd _).trans (gradedIndex_ladCell _)
  have hru (i : ℕ) : r i ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
    rw [CellScheme.mem_below, hrg, hugE]
    exact ⟨subset_rfl, by omega⟩
  have hrY (i : ℕ) : r i ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) := CellScheme.Rows.mem_below_of_le (hru i) hu'Y
  have hrung (i : ℕ) (hi : i < H) :
      θ (posTable R (i + 1)) = min (q (r i)) (q (Fin.castAdd _ u)) := by
    have hrr : (I.replicated g H Γ A B').rowAt (Fin.castAdd _ u) (r i) = posTable R (i + 1) := by
      refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hrowL (p i)).trans ?_)
      rw [hself i hi]
    rw [← hrr]
    exact hθrow _ (hru i)
  have hrrow (i : ℕ) (k : ℕ) :
      (I.replicated g H Γ A B').rowAt (r i) (r k) =
        ladderSource (min i (H - 1) + 1) (Scheme.baseIndex H (Scheme.rankProf
          (I.attachmentBase g).S H) a (Fin.natAdd _ (Scheme.ladderEquiv _ _ H (p k)))) := by
    refine (Scheme.rowAt_mirror_castAdd _ _).trans ?_
    rw [rowAt_ladCell_ladCell]
    rfl
  -- the top rung is positive
  have hu0 : q (Fin.castAdd _ u) ≠ ⊥ := fun h0 ↦ hx0 (le_bot_iff.mp (h0 ▸ hxu))
  have htop0 : q (r (H - 1)) ≠ ⊥ := by
    intro h0
    have h1 := hreadA x hxN.le
    have h2 := hrung (H - 1) (by omega)
    rw [show H - 1 + 1 = H by omega, h0, min_eq_left bot_le] at h2
    rw [min_eq_left hxu] at h1
    have h3 : θ (R x) ≤ θ (posTable R H) := hθ.monotone (htop x)
    rw [h1, h2] at h3
    exact hx0 (le_bot_iff.mp h3)
  have hpos : ∀ i < H, q (r i) ≠ ⊥ := by
    refine Scheme.rungs_ne_bot_of_top
      (isWellFormed_replicated (I := I) (g := g)).isWellFormed.grade_pos hq r
      (fun i _ ↦ hrg i) (fun i _ ↦ hrY i) (fun i hi ↦ ?_) (fun i hi hi0 ↦ ?_) htop0
    · rw [hrrow, hself i hi, show min i (H - 1) + 1 = i + 1 by omega]
    · rw [hrrow, hself (i - 1) (by omega), show min i (H - 1) + 1 = i + 1 by omega,
        show i - 1 + 1 = i by omega]
  refine ⟨Fin.castAdd _ u, hu'Y, congrArg Prod.snd hu'E, hxu, R, ?_, hR, θ, hθ, hreadA,
    fun y hy ↦ ?_⟩
  · have hm := Scheme.LadderBaseData.mem_towerCat.mp hRC
    rw [show N - 2 + 2 = N by omega] at hm
    exact Scheme.LadderBaseData.mem_towerCat.mpr hm
  · obtain ⟨i, hi, hiy⟩ := hval y hy
    rw [hiy, hrung i hi]
    intro h0
    rcases min_eq_bot.mp h0 with h' | h'
    · exact hpos i hi h'
    · exact hu0 h'

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The ambient's admission** at every grade, for requests calibrated on the class with a nonempty
root, when `⊥` is a value of the catalogue (so the catalogues are nonempty): from the threshold on,
the state of every section lawful below `(univ, j)` is admitted on its context and donor cells.  The
controller above the cap cell and its decoder (`Seed.exists_controller_decoder`) carry the reads of
the controller's admitted state to the section capped at the controller's value, which changes no
read. -/
theorem ambientAdmitted (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ0 : ⊥ ∈ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) (hn : 0 < n) (j : ℕ) :
    AmbientAdmitted I g H Γ B' hd Q j := by
  classical
  intro hNj q hq hcls hcap y
  have hne : ∀ k, ((I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (k + 2)).Nonempty :=
    fun k ↦ ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr
      ⟨fun _ ↦ hΓ0, Rows.isLawful_const_bot, I.attachAdmits_bot g hd Q _⟩⟩
  let qt : Fin (I.replicated g H Γ (I.attachAdmits g hd Q) B').card → Label.{u} := fun z ↦
    if h : z ∈ (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) then q ⟨z, h⟩ else ⊥
  have hqt_of (z : Fin (I.replicated g H Γ (I.attachAdmits g hd Q) B').card)
      (h : z ∈ (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) :
      qt z = q ⟨z, h⟩ := by simp only [qt, h, dite_true]
  have hqt : (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), j) fun d ↦ qt d := by
    convert hq using 1
    funext e
    exact hqt_of e.1 e.2
  have hN2 : 2 ≤ Q.threshold := by have := hQ.arity; omega
  have hNm : Q.threshold ≤ m + 1 := I.left.grade_le Q.cap
  -- the state of the ambient through `qt`
  have hamb_eq (c : Fin (I.attachment g).card) (hc : (I.attachment g).toCellScheme.grade c ≤ j) :
      ambientState H Γ (I.attachAdmits g hd Q) B' q c = qt (I.attachEmb g H Γ _ B' c) := by
    exact (ambientState_of_le (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B') (q := q)
      c hc).trans (hqt_of _ _).symm
  have hxg : (I.attachment g).toCellScheme.grade (I.attachCtxCell g Q.cap) = Q.threshold :=
    grade_attachCtxCell Q.cap
  have hx0 : qt (I.attachEmb g H Γ _ B' (I.attachCtxCell g Q.cap)) ≠ ⊥ := by
    rw [← hamb_eq _ (hxg.trans_le hNj)]
    exact hcap
  obtain ⟨u, huY, hug, hxu, R, hRC, -, θ, hθ, hread, hrefl⟩ := exists_controller_decoder hH hcard
    hne hN2 hNj hNm hqt hxg hx0
  set H' := qt u with hH'
  have hu0 : H' ≠ ⊥ := fun h0 ↦ hx0 (le_bot_iff.mp (h0 ▸ hxu))
  -- the reads of the state at the cells of grade at most the threshold
  have hctx (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ Q.threshold) :
      θ (I.attachHatAt g Q.threshold R (I.attachCtxCell g x)) =
        min (ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x)) H' := by
    have hcx : (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ Q.threshold :=
      (grade_attachCtxCell x).trans_le hx
    unfold attachHatAt
    rw [ite_eq_left hcx, hread _ hcx, hamb_eq _ (hcx.trans hNj)]
  have hdg (y : Fin d.card) :
      (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) ≤ Q.threshold := by
    have hg : (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) =
        d.toCellScheme.grade y :=
      Scheme.grade_faceCell (comap_toScheme_of_restrictFace
        (I.restrictFace_donor_attachmentType g hd)) y
    rw [hg]
    exact (d.grade_le y).trans hQ.arity
  have hdon (y : Fin d.card) :
      θ (I.attachHatAt g Q.threshold R (I.attachDonCell g hd y)) =
        min (ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachDonCell g hd y)) H' := by
    unfold attachHatAt
    rw [ite_eq_left (hdg y), hread _ (hdg y), hamb_eq _ ((hdg y).trans hNj)]
  -- the class and the cap of the state
  have hbelowN (x : Fin I.left.card)
      (hx : x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap)) :
      I.left.toCellScheme.grade x ≤ Q.threshold := hx.2
  have hRhat (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ Q.threshold) :
      I.attachHatAt g Q.threshold R (I.attachCtxCell g x) = R (I.attachCtxCell g x) := by
    unfold attachHatAt
    rw [ite_eq_left ((grade_attachCtxCell x).trans_le hx)]
  have hclsR : ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
      I.attachHatAt g Q.threshold R (I.attachCtxCell g x) = ⊥ ↔ I.left.label x = ⊥ := by
    intro x hx
    have hθx := hctx x (hbelowN x hx)
    rw [hRhat x (hbelowN x hx)] at hθx ⊢
    refine Iff.trans ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩ (hcls x hx)
    · rw [h0, hθ.map_bot] at hθx
      exact (min_eq_bot.mp hθx.symm).resolve_right hu0
    · by_contra hne0
      apply hrefl _ hne0
      rw [hθx]
      exact (congrArg (fun z ↦ min z H') h0).trans (min_eq_left bot_le)
  have hcapR : I.attachHatAt g Q.threshold R (I.attachCtxCell g Q.cap) ≠ ⊥ := by
    intro h0
    have h := hctx Q.cap le_rfl
    rw [h0, hθ.map_bot, hamb_eq _ (hxg.trans_le hNj), min_eq_left hxu] at h
    exact hx0 h.symm
  have hadmR := (Scheme.LadderBaseData.mem_towerCat.mp hRC).2.2 le_rfl hclsR hcapR y
  -- carried by the decoder, and uncapped
  have hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x) := fun i hi x ↦
    hθ.visibilityReplace_comm x Q.threshold (by simp [stepSuppressor_of_le]) i hi
  have hoff : y ∈ Q.exacts → Q.offset y ≤ Q.threshold := fun hy ↦ (hQ.ref y hy).2.1
  have hmap := hadmR.map hθ.monotone hθ.map_bot hθv hoff hQ.marker.2.1
  have hmap' : Q.CorrectAt
      (fun x ↦ min (ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x)) H') y
      (min (ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachDonCell g hd y)) H') := by
    have hm := hmap.congr (s' := fun x ↦
        min (ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x)) H')
      (hctx Q.cap le_rfl) (fun hy ↦ hctx _ (hQ.ref y hy).1) (hctx _ hQ.marker.1)
    exact (congrArg (Q.CorrectAt _ y) (hdon y)).mp hm
  refine hmap'.of_min ?_ ?_ hoff hQ.marker.2.1
  · rw [hamb_eq _ (hxg.trans_le hNj)]
    exact hxu
  · have ho := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hqt).1 u huY
    rw [hug] at ho
    exact ho

/-- **The context lift of the replicated scheme from the extension over the tower**, for requests
calibrated on the class with the labels pair admitted and the relative lift on the exact class,
over a legal donor with a nonempty root, when `⊥` is a value of the catalogue: the state lift holds
at every grade (`Seed.contextStateLiftR_attachAdmits`) since the ambient is admitted
(`Seed.ambientAdmitted`). -/
theorem hasContextLift_attachAdmits_tower (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hE : ∀ j, 1 ≤ j → j ≤ m + 1 → TowerExtension I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_attachAdmits_ext hte hdp hdL hn hd hQ hpair hrel
    (fun j _ _ ↦ ambientAdmitted hH hcard hΓ0 hd hQ hn j) hE

end Seed

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequests
import VaughtConjecture.Continuation.StableRecoveryReading
import VaughtConjecture.Stage.MarkedCap

/-!
# Cap requests at the reading type

Roadmap, Layer 3 (3.3: the private cap, the marker and the references of (R3) and (R4)).

The lemmas of `VaughtConjecture.Extension.CapRequests` at a compiled stage type: the reading type
`StableRecoveryReading.readingType ξ` at `λ_{ξ+1}` (three points; the reference cell `3` at
`({0, 1}, 1)` and the new cell `4` at `({1, 2}, 1)`, both labelled `λ_ξ + 1`; the cap `5` at
`({0, 1}, 2)` and the reading cell `8` at `(univ, 2)`, both labelled `⊤`; the cells `2` and `6`
of the donor face `{1, 2}` labelled `⊥`).  The requests `capReq` take the cap `5` with threshold
`N = 2`, the marker `3` with offset `R = 1`, `Z = {2, 6}`, `F = {4}` read through the reference
`3` at offset `1`, and `T = {8}`.

* The labels of the reading type are correct (`isCorrect_actual`), and the requests are graded by
  the grades of the cells.
* (R4) at the proper cap `λ_ξ + 2`: capping the labels at `λ_ξ + 2` keeps them correct, and the
  new cell is read as `λ_ξ + 1`, the cell `8` as at least `λ_ξ + 1`.
* A transformation by a capped witness keeps correctness (`IsCorrect.map`).
* **Recognition at the reading cell**: the row of the reading cell `8` reads the reference cell
  and the new cell at `1` and the cap at `ω + 2`, so it is correct for the requests carried to the
  cells below `8`, and locality at `8` (`IsCorrect.of_transformsTo`) makes the labels below `8`,
  capped at the label of `8`, correct.
* **The private type `P`** of `GatedExtensionCounterexample` (two points; dead cells `0`, `1`, `2`
  and two cells `3`, `4` of full scope and grade `2`), with the self-donor: a state is a pair
  `(sL, sR)` on the private and the donor copy, read here as one state `Sum.elim sL sR` on
  `Fin 5 ⊕ Fin 5`.  Capped correctness at `P` (`IsCapCorrectP`: cap and marker on the private copy,
  `Z = {1, 2}` and `T = {3, 4}` on the donor copy, nothing read exactly) is
  `CapRequests.IsCorrect` for the requests `reqP` (`isCapCorrectP_iff`, for `R < 2`), and its
  admission is `CapRequests.Admits` on the private copy (`isAdmittedP_iff`).  With the marker at
  the cap, correctness is the capped reading of the high cells, read off
  `CapRequests.isCorrect_iff_of_marker_eq_cap`.
* **A marked-cap context** (`IsMarkedCapContextAt`: a top cap `c` of grade `N > n + 1`, a marker
  `r`, and the row of `c` reading every root cell labelled `⊤` at least as the replacement at `N`
  with value `n + 1` of its value at `r`).  Its requests `ctxReq` take the cap `c`, the marker `r`
  with offset `n + 1`, and `T` the root cells labelled `⊤`.  The marked-cap clause is correctness
  of the row of `c` read as a state (`isCorrect_rowAt_of_isMarkedCapContextAt`), and the labels of
  the context are correct, every state with cap and marker `⊤` being correct exactly when it is
  `⊤` on `T` (`isCorrect_label_of_isMarkedCapContextAt`).
-/

universe u

namespace VaughtConjecture.CapRequestsExamples

open Label StageType Continuation.StableRecoveryReading CapRequests Realization

variable (ξ : Ordinal.{u})

/-- The requests at the reading type: cap `5` with threshold `2`, marker `3` with offset `1`,
`Z = {2, 6}`, `F = {4}` read through `3` at offset `1`, and `T = {8}`. -/
def capReq : CapRequests (Fin 10) where
  cap := 5
  N := 2
  R := 1
  R_lt_N := by decide
  Z := {2, 6}
  F := {4}
  T := {8}
  ref _ := 3
  off _ := 1
  marker := 3

/-- The requests are graded by the grades of the cells of the reading scheme. -/
theorem isGraded_capReq : capReq.IsGraded readingCells.grade where
  le_grade_cap := by decide
  off_le _ _ := (by decide : 1 ≤ 2)
  grade_le_of_mem_Z z hz := by
    rcases hz with rfl | rfl <;> decide
  grade_le_of_mem_F f hf := by
    rw [Set.mem_singleton_iff.mp hf]; decide
  grade_le_of_mem_T y hy := by
    rw [Set.mem_singleton_iff.mp hy]; decide
  grade_ref_le _ _ := (by decide : readingCells.grade 3 ≤ readingCells.grade 5)
  grade_marker_le := by decide

/-- **The labels of the reading type are correct** for `capReq`. -/
theorem isCorrect_readingType : capReq.IsCorrect (readingType.{u} ξ).label := by
  refine isCorrect_actual (readingType ξ) (fun z hz ↦ ?_) (fun f hf ↦ ?_) (fun y hy ↦ ?_)
  · rcases hz with rfl | rfl <;> rfl
  · obtain rfl : f = (4 : Fin 10) := hf
    exact ⟨blockStage ξ, isSuccPrelimit_blockStage ξ, 1, (by decide : 1 < 2), rfl, rfl⟩
  · obtain rfl : y = (8 : Fin 10) := hy
    rfl

/-- `λ_ξ + 2` is self-visible at `2`. -/
theorem isSelfVisible_two :
    IsSelfVisible 2 ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) :=
  isSelfVisible_coe_add (isSuccPrelimit_blockStage ξ) le_rfl

/-- `λ_ξ + 1 ≤ λ_ξ + 2`. -/
theorem one_le_two : ((blockStage ξ + (1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤
    ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by gcongr; exact_mod_cast (by decide : 1 ≤ 2)))

/-- **(R4) at a proper cap**: capped at `λ_ξ + 2`, the labels of the reading type stay correct;
the new cell `4` is read as `λ_ξ + 1`, and the cell `8` as at least `λ_ξ + 1`. -/
example :
    min ((readingType.{u} ξ).label (4 : Fin 10))
        ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) =
        ((blockStage ξ + (1 : ℕ) : Ordinal.{u}) : Label.{u}) ∧
      ((blockStage ξ + (1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤
        min ((readingType.{u} ξ).label (8 : Fin 10))
          ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) := by
  have hs := (isCorrect_readingType ξ).cap (fun _ _ ↦ (by decide : 1 ≤ 2)) (isSelfVisible_two ξ)
  have hcap : ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) ≤
      min ((readingType.{u} ξ).label capReq.cap)
        ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) := (min_top_left _).ge
  have hmarker : min ((readingType.{u} ξ).label capReq.marker)
      ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) =
        ((blockStage ξ + (1 : ℕ) : Ordinal.{u}) : Label.{u}) :=
    min_eq_left (one_le_two ξ)
  exact ⟨hs.label_eq_of_le (f := (4 : Fin 10)) rfl (isSuccPrelimit_blockStage ξ) le_rfl (k := 1)
    (by decide : 1 < 2) hmarker (by decide : 1 < 2) hcap,
    hs.le_label (y := (8 : Fin 10)) rfl (isSuccPrelimit_blockStage ξ) (i := 1)
      (by decide : 1 < 2) hmarker ((one_le_two ξ).trans hcap)⟩

/-- The requests with the marker at the cap `5`: cap and marker `⊤`. -/
def capReqTop : CapRequests (Fin 10) := { capReq with marker := 5 }

/-- **(R3) at cap and marker `⊤`**: the cell `8` of `T` is `⊤`, and the new cell `4` of `F` is
the replacement of its reference. -/
example : (readingType.{u} ξ).label (8 : Fin 10) = ⊤ ∧
    (readingType.{u} ξ).label (4 : Fin 10) =
      visibilityReplace 2 1 ((readingType.{u} ξ).label (3 : Fin 10)) := by
  have hs : capReqTop.IsCorrect (readingType.{u} ξ).label := by
    refine isCorrect_actual (readingType ξ) (fun z hz ↦ ?_) (fun f hf ↦ ?_) (fun y hy ↦ ?_)
    · rcases hz with rfl | rfl <;> rfl
    · obtain rfl : f = (4 : Fin 10) := hf
      exact ⟨blockStage ξ, isSuccPrelimit_blockStage ξ, 1, (by decide : 1 < 2), rfl, rfl⟩
    · obtain rfl : y = (8 : Fin 10) := hy
      rfl
  obtain ⟨-, hF, hT⟩ := (isCorrect_iff_of_eq_top rfl rfl).mp hs
  exact ⟨hT (8 : Fin 10) rfl, hF (4 : Fin 10) rfl⟩

/-- **A capped witness keeps correctness**: the identity shifter with the suppressor `λ_ξ + 2` at
the grades at most `2` and `⊥` above. -/
example : capReq.IsCorrect fun d ↦
    min (id ((readingType.{u} ξ).label d))
      ((fun n ↦ if n ≤ 2 then min ⊤ ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u})
        else ⊥) (readingCells.grade d)) :=
  (isCorrect_readingType ξ).map isGraded_capReq (IsWitness.id_top.cap (isSelfVisible_two ξ))

/-! ### Recognition at the reading cell -/

/-- The cells below the reading cell `8`. -/
abbrev Below8 := ↥(readingCells.below (readingCells.gradedIndex 8))

/-- Every cell other than `9` lies below the reading cell `8`. -/
theorem mem_below8 : ∀ d : Fin 10, d ≠ 9 → d ∈ readingCells.below (readingCells.gradedIndex 8) := by
  intro d
  rw [CellScheme.mem_below, Prod.le_def]
  revert d
  decide

/-- The requests `capReq` carried to the cells below the reading cell. -/
def capReq8 : CapRequests Below8 where
  cap := ⟨5, mem_below8 5 (by decide)⟩
  N := 2
  R := 1
  R_lt_N := by decide
  Z := {⟨2, mem_below8 2 (by decide)⟩, ⟨6, mem_below8 6 (by decide)⟩}
  F := {⟨4, mem_below8 4 (by decide)⟩}
  T := {⟨8, mem_below8 8 (by decide)⟩}
  ref _ := ⟨3, mem_below8 3 (by decide)⟩
  off _ := 1
  marker := ⟨3, mem_below8 3 (by decide)⟩

/-- The carried requests are graded by the grades of the cells below the reading cell. -/
theorem isGraded_capReq8 : capReq8.IsGraded fun d : Below8 ↦ readingCells.grade d.1 where
  le_grade_cap := (by decide : 2 ≤ readingCells.grade 5)
  off_le _ _ := (by decide : 1 ≤ 2)
  grade_le_of_mem_Z z hz := by
    rcases hz with rfl | rfl
    · exact (by decide : readingCells.grade 2 ≤ readingCells.grade 5)
    · exact (by decide : readingCells.grade 6 ≤ readingCells.grade 5)
  grade_le_of_mem_F f hf := by
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact (by decide : readingCells.grade 4 ≤ readingCells.grade 5)
  grade_le_of_mem_T y hy := by
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact (by decide : readingCells.grade 8 ≤ readingCells.grade 5)
  grade_ref_le _ _ := (by decide : readingCells.grade 3 ≤ readingCells.grade 5)
  grade_marker_le := (by decide : readingCells.grade 3 ≤ readingCells.grade 5)

/-- The row of the reading cell is correct for the carried requests: it reads the reference cell
and the new cell at `1`, the cap and itself at `ω + 2`, and the dead cells at `⊥`. -/
theorem isCorrect_row8 : capReq8.IsCorrect ((readingType.{u} ξ).rows.row (8 : Fin 10)) := by
  refine isCorrect_of_forall (fun z hz ↦ ?_) (fun f hf ↦ ?_) (fun y hy ↦ ?_)
  · rcases hz with rfl | rfl <;> rfl
  · obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨Ordinal.omega0 * ((0 : ℕ) : Ordinal.{u}),
      Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _), 1, (by decide : 1 < 2),
      rfl, rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp hy
    exact min_le_right _ _

/-- **Recognition at the reading cell**: locality at `8` makes the labels below `8`, capped at
the label of `8`, correct for the carried requests. -/
example : capReq8.IsCorrect fun d : Below8 ↦
    min ((readingType.{u} ξ).label d.1) ((readingType.{u} ξ).label (8 : Fin 10)) :=
  (isCorrect_row8 ξ).of_transformsTo isGraded_capReq8
    ((readingType ξ).isLawful.locality (8 : Fin 10))

/-! ### The private type `P` of the gated extension counterexample -/

/-- The donor cells requested `⊥` at `P`: the dead cells on the new point. -/
def selfZ : Finset (Fin 5) := {1, 2}

/-- The donor cells requested high at `P`: the two cells of full scope. -/
def selfT : Finset (Fin 5) := {3, 4}

/-- **The bottom class** of the private side at `P`: `⊥` exactly at the dead cells. -/
def InBottomClassP (sL : Fin 5 → Label.{u}) : Prop :=
  ∀ d, sL d = ⊥ ↔ d ∈ ({0, 1, 2} : Finset (Fin 5))

/-- **Capped correctness at `P`** of a state (`sL` on the private copy, `sR` on the donor copy)
for the cap `C`, the marker `a` and the marker offset `R`, at the threshold `N = 2`. -/
def IsCapCorrectP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧
    ∀ y ∈ selfT, min (visibilityReplace 2 R (sL a)) (sL C) ≤ min (sR y) (sL C)

/-- **Admission at `P`**: correct as soon as the private side is in the bottom class. -/
def IsAdmittedP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  InBottomClassP sL → IsCapCorrectP C a R sL sR

/-- The requests at `P` on the private copy and the donor copy `Fin 5 ⊕ Fin 5`: the cap `C` and
the marker `a` on the private copy, threshold `2`, offset `R < 2`, `Z` and `T` the donor copies of
`selfZ` and `selfT`, and no cell read exactly. -/
def reqP (C a : Fin 5) (R : ℕ) (hR : R < 2) : CapRequests (Fin 5 ⊕ Fin 5) where
  cap := .inl C
  N := 2
  R := R
  R_lt_N := hR
  Z := Sum.inr '' (selfZ : Set (Fin 5))
  F := ∅
  T := Sum.inr '' (selfT : Set (Fin 5))
  ref := id
  off _ := 0
  marker := .inl a

variable {C a : Fin 5} {R : ℕ} {sL sR : Fin 5 → Label.{u}}

/-- **Capped correctness at `P` is an instance of `CapRequests.IsCorrect`**, for `R < 2`. -/
theorem isCapCorrectP_iff (hR : R < 2) :
    IsCapCorrectP C a R sL sR ↔ (reqP C a R hR).IsCorrect (Sum.elim sL sR) := by
  constructor
  · rintro ⟨hZ, hT⟩
    refine ⟨?_, fun f hf ↦ hf.elim, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hZ z hz
    · rintro _ ⟨y, hy, rfl⟩
      exact hT y hy
  · intro h
    exact ⟨fun z hz ↦ h.eq_bot _ ⟨z, hz, rfl⟩, fun y hy ↦ h.markerValue_le _ ⟨y, hy, rfl⟩⟩

/-- The bottom class at `P` is `InBottomClass` on the private copy. -/
theorem inBottomClassP_iff :
    InBottomClassP sL ↔ InBottomClass (Set.range Sum.inl)
      (Sum.inl '' ((({0, 1, 2} : Finset (Fin 5))) : Set (Fin 5))) (Sum.elim sL sR) := by
  constructor
  · rintro h _ ⟨d, rfl⟩
    simpa using h d
  · intro h d
    simpa using h (.inl d) ⟨d, rfl⟩

/-- **Admission at `P` is an instance of `CapRequests.Admits`**, for `R < 2`. -/
theorem isAdmittedP_iff (hR : R < 2) :
    IsAdmittedP C a R sL sR ↔ (reqP C a R hR).Admits (Set.range Sum.inl)
      (Sum.inl '' ((({0, 1, 2} : Finset (Fin 5))) : Set (Fin 5))) (Sum.elim sL sR) := by
  rw [IsAdmittedP, CapRequests.Admits, inBottomClassP_iff, isCapCorrectP_iff hR]

/-- **With the marker at the cap, correctness at `P` is the capped reading** of the high cells,
read off `CapRequests.isCorrect_iff_of_marker_eq_cap`. -/
example (hR : R < 2) (hC : IsSelfVisible 2 (sL C)) :
    IsCapCorrectP C C R sL sR ↔
      (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧ ∀ y ∈ selfT, sL C ≤ sR y := by
  rw [isCapCorrectP_iff hR, isCorrect_iff_of_marker_eq_cap rfl hC]
  constructor
  · rintro ⟨hZ, -, hT⟩
    exact ⟨fun z hz ↦ hZ _ ⟨z, hz, rfl⟩, fun y hy ↦ hT _ ⟨y, hy, rfl⟩⟩
  · rintro ⟨hZ, hT⟩
    refine ⟨?_, fun f hf ↦ hf.elim, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hZ z hz
    · rintro _ ⟨y, hy, rfl⟩
      exact hT y hy

/-! ### A marked-cap context -/

section MarkedCap

variable {α : Ordinal.{u}} {k n : ℕ}

/-- The data of a marked-cap context along `h` with top cap `c` and marker `r`. -/
def IsMarkedCapContextAt (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c r : Fin t'.card) :
    Prop :=
  t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    ∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a

/-- The requests of a marked-cap context: the top cap `c` with threshold its grade `N`, the
marker `r` with offset `n + 1 < N`, `T` the cells of the root labelled `⊤`, and the cells `Z` and
`F` empty. -/
def ctxReq (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c r : Fin t'.card)
    (hN : n + 1 < t'.toCellScheme.grade c) : CapRequests (Fin t'.card) where
  cap := c
  N := t'.toCellScheme.grade c
  R := n + 1
  R_lt_N := hN
  Z := ∅
  F := ∅
  T := {a | a ∈ t'.visibleCells h ∧ t'.label a = ⊤}
  ref := id
  off _ := 0
  marker := r

/-- **The marked-cap clause is correctness of the row of the top cap**: in a marked-cap context,
the row of the top cap, read as a state, is correct for the requests of the context. -/
theorem isCorrect_rowAt_of_isMarkedCapContextAt {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c r : Fin t'.card} (hctx : IsMarkedCapContextAt t' h c r) :
    (ctxReq t' h c r hctx.2.2.1).IsCorrect (t'.rowAt c) where
  eq_bot _ hz := hz.elim
  eq_refValue _ hf := hf.elim
  markerValue_le y hy := min_le_min_right _ (hctx.2.2.2 y hy.1 hy.2)

/-- **The actual labels of a marked-cap context are a template**: with the top cap and the
marker labelled `⊤`, the labels of the context are correct for the requests of the context, and
every state with cap and marker `⊤` is correct exactly when it is `⊤` at the cells of `T`. -/
theorem isCorrect_label_of_isMarkedCapContextAt {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c r : Fin t'.card} (hctx : IsMarkedCapContextAt t' h c r) :
    (ctxReq t' h c r hctx.2.2.1).IsCorrect t'.label ∧
      ∀ s : Fin t'.card → Label.{u}, s c = ⊤ → s r = ⊤ →
        ((ctxReq t' h c r hctx.2.2.1).IsCorrect s ↔
          ∀ y ∈ (ctxReq t' h c r hctx.2.2.1).T, s y = ⊤) := by
  refine ⟨isCorrect_actual t' (fun _ hz ↦ hz.elim) (fun _ hf ↦ hf.elim) fun _ hy ↦ hy.2,
    fun s hc hr ↦ ?_⟩
  rw [isCorrect_iff_of_eq_top hc hr]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨fun _ hz ↦ hz.elim, fun _ hf ↦ hf.elim, h⟩⟩

/-- The top cap and the marker of a marked-cap context are labelled `⊤`. -/
example {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {c r : Fin t'.card}
    (hctx : IsMarkedCapContextAt t' h c r) : t'.label c = ⊤ ∧ t'.label r = ⊤ :=
  ⟨hctx.1.2.1, hctx.2.1.1⟩

end MarkedCap

end VaughtConjecture.CapRequestsExamples

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.ENat.Lattice
import VaughtConjecture.Stage.Legal

/-!
# Forcing thresholds and the provisional offset

Roadmap, Layer 1 (stage types, exact face maps, stage reduction) and Layer 4, outputs 1–2 (the
provisional finite offset of a cell, determined by finite data); semantic contract, item 3.
Everything here concerns stage types only: no realization and no model is involved.

Throughout, `β` is a stage that is zero or a limit (`hβ : Order.IsSuccPrelimit β`) and `α` is a
second stage; in the application `β = λ_η` and `α = λ_{η+1}` are consecutive block stages.

**Forcing.**  Let `q` be a stage type at `β` on `m` points, `f : Fin k ↪ Fin m` an embedding of
coordinates along which `q` restricts to `p` (`restrictFace f q = some p`), and `d` a cell of `p`.
The pair `(q, f)` **forces** the threshold `n : ℕ` at `d` (`StageType.ForcesThreshold α hβ q f p d
n`) when every stage type `Q` at `α` whose reduction to `β` is `q` has, on its face `P` along `f`,
a label at least `β + n` at the cell of `P` at the position of `d`.  The quantifier ranges over all
stage types at `α`: no realization, and no legality (legality depends only on the scheme, which
`Q` shares with `q`).  Forcing reads only the finite data `(q, f, p, d)`.

* Forcing is downward closed in `n` (`ForcesThreshold.mono`).
* **Forcing is monotone along extensions** of `q` (`ForcesThreshold.trans_face`): if `q` is the
  face of `q'` along `g`, a threshold forced at `(q, f)` is forced at `(q', f.trans g)`.  Only
  the commutation of reduction with face maps (`restrictFace_reduce`) and the composition law of
  face maps (`restrictFace_trans`) are used.
* **The order law** (`forcesThreshold_of_le_grade`): if the label of `d` in `p` is the formal top
  and `n` is at most the grade of `d`, then `(q, f)` forces `n`.  A label at least `β` that is
  self-visible at the grade `g` of its cell is at least `β + g`, since `β` is a multiple of `ω`
  (`Label.coe_add_le_of_isSelfVisible`, in `VaughtConjecture.Label.Visibility`).
* **A tie** (`forcesThreshold_of_row_le`): if a cell `C` of `q` is labelled the formal top, the
  cell `e` of `q` transported from `d` lies below `C`, and the row of `C` is at least as large at
  `e` as at `C`, then `(q, f)` forces the grade of `C`.  Locality of `Q` at `C`
  (`Label.TransformsTo.le_of_le`) gives that the label of `e` is at least that of `C`, which is at
  least `β` plus the grade of `C` by the order law.

**The provisional offset** of `d` at `(q, f)` (`StageType.provisionalOffset`) is the supremum in
`ℕ∞` of the thresholds forced at `d`.  When `q` restricts to `p` along `f` and `d` reduces to the
formal top, `n` is at most the provisional offset exactly when `(q, f)` forces `n`
(`le_provisionalOffset_iff`); for `n ≠ 0` no hypothesis is needed
(`natCast_le_provisionalOffset_iff`).  Provisional offsets are monotone along extensions
(`provisionalOffset_le_trans_face`).  By the order law the provisional offset is at least the
grade of `d`.  A single pair `(q, f)` is not claimed here to force only finitely many thresholds;
the value `⊤` of a supremum over many pairs is allowed.

**Faces of the root and attained offsets.**

* A *lift* of `q` is a stage type at `α` reducing to `q`.  A lift of `q` restricts along `f` to a
  lift of `p` (`StageType.exists_restrictFace_reduce_eq`, in `VaughtConjecture.Stage.Basic`).
* **Forcing at a face of the root** (`ForcesThreshold.trans_comap_iff`): if `q` restricts to `p`
  along `h` and `f` spans a closed face of `p`, forcing at `(q, f.trans h)` for the root
  `p.comap f hf` at a cell `i` is forcing at `(q, h)` for `p` at the transported cell
  `p.cellMap f i`.
* **The provisional offset is attained** (`exists_lift_label_eq_ofOffset`): if `q` restricts to
  `p` along `f` and `d` is labelled the formal top in `p`, some stage type at `β + ω` reducing to
  `q` carries, at the position of `d` on its face along `f`, exactly the label `Label.ofOffset β`
  of the provisional offset.  A finite offset `o` is forced and `o + 1` is not, so a lift
  witnessing the failure of `o + 1` has the label `β + o`; an infinite offset makes every lift
  carry the formal top there.  This reading by lifts applies only when `q` restricts to `p` along
  `f`: otherwise `(q, f)` forces no threshold at `d`, its provisional offset is `0`, and nothing is
  said about lifts.

These are used for comparing stable offsets along faces of a cover and for realizing the stable
labels by lifts (roadmap, Layer 4, output 1; `Realization.stableOffset_comap` and
`Realization.locality_stableSection`, in `VaughtConjecture.Continuation.Candidate`).

**Offsets as labels.**  `Label.ofOffset β o` is `β + o` for a finite `o` and the formal top for
`o = ⊤` (`Label.ofOffset_eq_top_iff`); its thresholds are those of `o`
(`Label.coe_add_le_ofOffset_iff`), it lies in `[β, β + ω) ∪ {⊤}` (`Label.le_ofOffset`,
`Label.atStage_ofOffset`), and it is never `β + ω` (`Label.ofOffset_ne_coe_add_omega0`): an
infinite offset is the formal top, not `β + ω`.

**Forced thresholds at twins.**  For `β + ω ≤ α` and `K` at least the grade of every cell of `q`
labelled the formal top, the labelling `min (q.label d) (β + K)` is a lift of `q` to `α`
(`StageType.capLift`, `StageType.capLift_reduce`); it is lawful because `β + K` is self-visible
at the grade of each such cell ([Kni26, Lemma 2.5.8]).  For a legal `q` and cells `s₀`, `t₀` of
`q` with `s₀` labelled the formal top, the scope of `s₀` in that of `t₀` and equal grades, every
threshold `N` forced at `s₀` by `q` itself is forced at some cell labelled the formal top at the
graded index of `t₀` (`StageType.exists_forcesThreshold_twin`):

* for `N` at most the grade of `s₀`, at the cell given by availability of `q`, by the order law;
* otherwise the capped lift gives `N ≤ K` for the largest grade `K` of a cell labelled the formal
  top; completeness and availability of `q` give a cell `D` of full scope and grade `K` labelled
  the formal top; availability of the row of `D`, lawful below `D` by consistency of the rows,
  gives a cell `w` at the graded index of `t₀` at which the row of `D` is at least its value at
  `s₀`; and locality of every lift `Q` at `D` gives `min (Q s₀) (Q D) ≤ Q w`, while
  `Q D ≥ β + K ≥ β + N` by the order law.

The same holds for a rooted cover `(q, f)` with root `p`, the cells taken in `p`
(`StageType.exists_forcesThreshold_twin_face`): the cell found in `q` lies in the face spanned by
`f`.  This is the availability of the stable section at twins
(`Realization.availability_stableSection_of_hasLegalTypes`, in
`VaughtConjecture.Continuation.Candidate`).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Ordinal

/-- For a positive natural number `n`, `n` is at most a supremum in `ℕ∞` exactly when it is at most
one of its terms. -/
theorem natCast_le_iSup_iff_of_ne_zero {ι : Sort*} {f : ι → ℕ∞} {n : ℕ} (hn : n ≠ 0) :
    (n : ℕ∞) ≤ ⨆ i, f i ↔ ∃ i, (n : ℕ∞) ≤ f i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [Nat.cast_succ, ENat.natCast_add_one_le_iff, lt_iSup_iff]

namespace Label

variable {β : Ordinal.{u}} {x : Label.{u}} {n : ℕ} {o : ℕ∞}

/-- The **label of an offset** `o : ℕ∞` above `β`: `β + o` for finite `o`, the formal top for
`o = ⊤`. -/
noncomputable def ofOffset (β : Ordinal.{u}) (o : ℕ∞) : Label.{u} :=
  if o = ⊤ then ⊤ else ((β + o.toNat : Ordinal.{u}) : Label.{u})

/-- The label of the infinite offset is the formal top. -/
@[simp] theorem ofOffset_top : ofOffset β ⊤ = ⊤ := ite_eq_left rfl

/-- The label of a finite offset `n` is `β + n`. -/
@[simp] theorem ofOffset_natCast (n : ℕ) :
    ofOffset β n = ((β + n : Ordinal.{u}) : Label.{u}) := by
  simp [ofOffset]

/-- The label of an offset is monotone in the offset. -/
theorem ofOffset_mono : Monotone (ofOffset β) := by
  intro o o' h
  induction o' using ENat.recTopCoe with
  | top => exact ofOffset_top ▸ le_top
  | coe m' =>
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top m') h)
    rw [ofOffset_natCast, ofOffset_natCast]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      (add_le_add_right (Nat.cast_le.mpr (ENat.natCast_le_natCast.mp h)) _))

/-- `β ≤ β + n` as labels. -/
theorem coe_le_coe_add (β : Ordinal.{u}) (n : ℕ) :
    (β : Label.{u}) ≤ ((β + n : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

/-- The label of an offset is the formal top exactly when the offset is infinite. -/
@[simp] theorem ofOffset_eq_top_iff : ofOffset β o = ⊤ ↔ o = ⊤ := by
  induction o using ENat.recTopCoe with
  | top => simp
  | coe m =>
    rw [ofOffset_natCast]
    exact iff_of_false (fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h))
      (ENat.natCast_ne_top m)

/-- **The thresholds of the label of an offset** are those of the offset. -/
theorem coe_add_le_ofOffset_iff :
    ((β + n : Ordinal.{u}) : Label.{u}) ≤ ofOffset β o ↔ (n : ℕ∞) ≤ o := by
  induction o using ENat.recTopCoe with
  | top => simp
  | coe m =>
    rw [ofOffset_natCast, WithBot.coe_le_coe, WithTop.coe_le_coe, add_le_add_iff_left,
      Nat.cast_le, Nat.cast_le]

/-- The label of an offset is at least `β`. -/
theorem le_ofOffset : (β : Label.{u}) ≤ ofOffset β o := by
  simpa using coe_add_le_ofOffset_iff (β := β) (n := 0) (o := o) |>.mpr zero_le

/-- The label of an offset occurs at the stage `β + ω`. -/
theorem atStage_ofOffset : AtStage (β + ω) (ofOffset β o) := by
  induction o using ENat.recTopCoe with
  | top => exact Or.inr ofOffset_top
  | coe m =>
    rw [ofOffset_natCast]
    exact atStage_coe.mpr (add_lt_add_right (natCast_lt_omega0 m) β)

/-- **An infinite offset is not `β + ω`**: the label of an offset is never `β + ω`. -/
theorem ofOffset_ne_coe_add_omega0 : ofOffset β o ≠ ((β + ω : Ordinal.{u}) : Label.{u}) := by
  induction o using ENat.recTopCoe with
  | top => exact fun h ↦ WithTop.top_ne_coe (WithBot.coe_injective h)
  | coe m =>
    rw [ofOffset_natCast]
    exact fun h ↦ (add_lt_add_right (natCast_lt_omega0 m) β).ne
      (WithTop.coe_injective (WithBot.coe_injective h))

end Label

namespace StageType

variable {α β : Ordinal.{u}} {k m m' : ℕ} {q : StageType.{u} β m} {f : Fin k ↪ Fin m}
  {p : StageType.{u} β k} {d : Fin p.card} {n n' : ℕ}

/-! ### Forcing -/

/-- The pair `(q, f)` **forces** the threshold `n` at the cell `d` of `p`: `q` restricts to `p`
along `f`, and every stage type `Q` at `α` reducing to `q` at `β` has, on its face along `f`, a
label at least `β + n` at the position of `d`. -/
def ForcesThreshold (α : Ordinal.{u}) (hβ : Order.IsSuccPrelimit β) (q : StageType.{u} β m)
    (f : Fin k ↪ Fin m) (p : StageType.{u} β k) (d : Fin p.card) (n : ℕ) : Prop :=
  restrictFace f q = some p ∧
    ∀ (Q : StageType.{u} α m) (P : StageType.{u} α k), Q.reduce hβ = q →
      restrictFace f Q = some P → ∀ i : Fin P.card, (i : ℕ) = d →
        ((β + n : Ordinal.{u}) : Label.{u}) ≤ P.label i

variable {hβ : Order.IsSuccPrelimit β}

/-- A pair forcing a threshold restricts to the root along the embedding. -/
theorem ForcesThreshold.restrictFace_eq (h : ForcesThreshold α hβ q f p d n) :
    restrictFace f q = some p :=
  h.1

/-- **Forcing is downward closed** in the threshold. -/
theorem ForcesThreshold.mono (h : ForcesThreshold α hβ q f p d n) (hn : n' ≤ n) :
    ForcesThreshold α hβ q f p d n' :=
  ⟨h.1, fun Q P hQ hP i hi ↦ le_trans (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
    (add_le_add_right (Nat.cast_le.mpr hn) β))) (h.2 Q P hQ hP i hi)⟩

/-- **Forcing is monotone along extensions**: if `q` is the face of `q'` along `g`, a threshold
forced at `(q, f)` is forced at `(q', f.trans g)`. -/
theorem ForcesThreshold.trans_face {q' : StageType.{u} β m'} {g : Fin m ↪ Fin m'}
    (hg : restrictFace g q' = some q) (h : ForcesThreshold α hβ q f p d n) :
    ForcesThreshold α hβ q' (f.trans g) p d n := by
  refine ⟨(restrictFace_trans q' g f hg).symm.trans h.1, fun Q' P hQ' hP ↦ ?_⟩
  have hQ := restrictFace_reduce Q' g hβ
  rw [hQ', hg] at hQ
  obtain ⟨Q, hQg, hQq⟩ := Option.map_eq_some_iff.mp hQ.symm
  exact h.2 Q P hQq ((restrictFace_trans Q' g f hQg).trans hP)

/-- **The order law**: if `q` restricts to `p` along `f` and the label of `d` in `p` is the formal
top, then `(q, f)` forces every threshold up to the grade of `d`. -/
theorem forcesThreshold_of_le_grade (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (hn : n ≤ p.toCellScheme.grade d) : ForcesThreshold α hβ q f p d n := by
  refine ⟨hfp, fun Q P hQ hP i hi ↦ ?_⟩
  have hPp : P.reduce hβ = p := by
    have h := restrictFace_reduce Q f hβ
    rw [hQ, hfp, hP, Option.map_some] at h
    exact (Option.some_injective _ h).symm
  subst hPp
  have hid : i = d := Fin.ext hi
  subst hid
  exact Label.coe_add_le_of_isSelfVisible hβ (Label.reduce_eq_top_iff.mp hd)
    ((P.isLawful.orderly i).mono hn)

/-- Every pair restricting to `p` forces the threshold `0` at a cell labelled the formal top. -/
theorem forcesThreshold_zero (hfp : restrictFace f q = some p) (hd : p.label d = ⊤) :
    ForcesThreshold α hβ q f p d 0 :=
  forcesThreshold_of_le_grade hfp hd (Nat.zero_le _)

/-- **A tie forces the grade of the tied cell**: if a cell `C` of `q` is labelled the formal top,
the cell `e` of `q` transported from `d` along `f` lies below `C`, and the row of `C` is at least
as large at `e` as at `C`, then `(q, f)` forces the grade of `C`. -/
theorem forcesThreshold_of_row_le (hfp : restrictFace f q = some p) {C e : Fin q.card}
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e)
    (hC : q.label C = ⊤) (heC : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex C))
    (hrow : q.rows.row C ⟨C, q.toCellScheme.mem_below_gradedIndex C⟩ ≤ q.rows.row C ⟨e, heC⟩) :
    ForcesThreshold α hβ q f p d (q.toCellScheme.grade C) := by
  refine ⟨hfp, fun Q P hQ hP i hi ↦ ?_⟩
  subst hQ
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff Q f).mp hP
  have hCe : Q.label C ≤ Q.label e := by
    have h := (Q.isLawful.locality C).le_of_le (d := ⟨C, Q.toCellScheme.mem_below_gradedIndex C⟩)
      (d' := ⟨e, heC⟩) hrow heC.2
    rw [min_self] at h
    exact h.trans (min_le_left _ _)
  have hCβ := Label.coe_add_le_of_isSelfVisible hβ (Label.reduce_eq_top_iff.mp hC)
    (Q.isLawful.orderly C)
  have hie : Q.cellMap f i = e := he i hi
  rw [comap_label, hie]
  exact hCβ.trans hCe

/-! ### The provisional offset -/

/-- The **provisional offset** of the cell `d` at `(q, f)`: the supremum in `ℕ∞` of the
thresholds forced at `d`. -/
noncomputable def provisionalOffset (α : Ordinal.{u}) (hβ : Order.IsSuccPrelimit β)
    (q : StageType.{u} β m) (f : Fin k ↪ Fin m) (p : StageType.{u} β k) (d : Fin p.card) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ForcesThreshold α hβ q f p d n), (n : ℕ∞)

/-- A forced threshold is at most the provisional offset. -/
theorem ForcesThreshold.le_provisionalOffset (h : ForcesThreshold α hβ q f p d n) :
    (n : ℕ∞) ≤ provisionalOffset α hβ q f p d :=
  le_iSup₂ (f := fun n (_ : ForcesThreshold α hβ q f p d n) ↦ (n : ℕ∞)) n h

/-- **Provisional offsets are monotone along extensions**: if `q` is the face of `q'` along `g`,
the provisional offset at `(q, f)` is at most that at `(q', f.trans g)`. -/
theorem provisionalOffset_le_trans_face {q' : StageType.{u} β m'} {g : Fin m ↪ Fin m'}
    (hg : restrictFace g q' = some q) :
    provisionalOffset α hβ q f p d ≤ provisionalOffset α hβ q' (f.trans g) p d :=
  iSup₂_le fun _ h ↦ (h.trans_face hg).le_provisionalOffset

/-- A positive `n` is at most the provisional offset exactly when it is forced. -/
theorem natCast_le_provisionalOffset_iff (hn : n ≠ 0) :
    (n : ℕ∞) ≤ provisionalOffset α hβ q f p d ↔ ForcesThreshold α hβ q f p d n := by
  refine ⟨fun h ↦ ?_, ForcesThreshold.le_provisionalOffset⟩
  obtain ⟨n', hn'⟩ := (natCast_le_iSup_iff_of_ne_zero hn).mp h
  obtain ⟨h', hle⟩ := (natCast_le_iSup_iff_of_ne_zero hn).mp hn'
  exact h'.mono (Nat.cast_le.mp hle)

/-- **The provisional offset characterizes forcing**: if `q` restricts to `p` along `f` and `d`
is labelled the formal top in `p`, then `n` is at most the provisional offset exactly when
`(q, f)` forces `n`. -/
theorem le_provisionalOffset_iff (hfp : restrictFace f q = some p) (hd : p.label d = ⊤) :
    (n : ℕ∞) ≤ provisionalOffset α hβ q f p d ↔ ForcesThreshold α hβ q f p d n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨fun _ ↦ forcesThreshold_zero hfp hd, ForcesThreshold.le_provisionalOffset⟩
  · exact natCast_le_provisionalOffset_iff hn

/-- **The order-law lower bound**: the provisional offset is at least the grade of `d`. -/
theorem grade_le_provisionalOffset (hfp : restrictFace f q = some p) (hd : p.label d = ⊤) :
    (p.toCellScheme.grade d : ℕ∞) ≤ provisionalOffset α hβ q f p d :=
  (forcesThreshold_of_le_grade hfp hd le_rfl).le_provisionalOffset

/-! ### Faces of the root and lifts attaining the provisional offset -/

/-- **Forcing at a face of the root is forcing at the transported cell**: if `q` restricts to `p`
along `h` and `f` spans a closed face of `p`, then `(q, f.trans h)` forces `n` at the cell `i` of
the face `p.comap f hf` exactly when `(q, h)` forces `n` at the cell `p.cellMap f i` of `p`.
Cells are matched by position. -/
theorem ForcesThreshold.trans_comap_iff {j : ℕ} {h : Fin k ↪ Fin m}
    (hp : restrictFace h q = some p) {f : Fin j ↪ Fin k}
    (hf : Finset.univ.map f ∈ p.toCellScheme.faces) (i : Fin (p.comap f hf).card) :
    ForcesThreshold α hβ q (f.trans h) (p.comap f hf) i n ↔
      ForcesThreshold α hβ q h p (p.cellMap f i) n := by
  have hq : restrictFace (f.trans h) q = some (p.comap f hf) := by
    rw [← restrictFace_trans q h f hp, restrictFace_of_mem p f hf]
  refine ⟨fun ⟨_, H⟩ ↦ ⟨hp, fun Q P hQ hP i' hi' ↦ ?_⟩,
    fun ⟨_, H⟩ ↦ ⟨hq, fun Q P' hQ hP' i' hi' ↦ ?_⟩⟩
  · obtain ⟨P₀, hP₀, hPp⟩ := exists_restrictFace_reduce_eq hp hQ
    rw [hP₀] at hP
    cases hP
    subst hPp
    have hf' : Finset.univ.map f ∈ P.toCellScheme.faces := hf
    have h' : ((β + n : Ordinal.{u}) : Label.{u}) ≤ P.label (P.cellMap f i) := H Q
      (P.comap f hf') hQ (by rw [← restrictFace_trans Q h f hP₀, restrictFace_of_mem P f hf']) i rfl
    exact h'.trans_eq (congrArg P.label (Fin.ext hi'.symm))
  · obtain ⟨P, hP, hPp⟩ := exists_restrictFace_reduce_eq hp hQ
    subst hPp
    have hf' : Finset.univ.map f ∈ P.toCellScheme.faces := hf
    rw [← restrictFace_trans Q h f hP, restrictFace_of_mem P f hf'] at hP'
    obtain rfl := Option.some_injective _ hP'
    rw [comap_label]
    exact H Q P hQ hP _ (congrArg Fin.val (congrArg (P.cellMap f) (Fin.ext hi')))

/-- **A lift attaining the provisional offset**: if `q` restricts to `p` along `f` and `d` is
labelled the formal top in `p`, some stage type at `β + ω` reducing to `q` has, on its face along
`f`, the label `β + o` at the position of `d`, where `o` is the provisional offset of `d` at
`(q, f)` (the formal top when `o = ⊤`).  For a finite offset `o`, a lift witnessing that `o + 1` is
not forced has this label, since `o` is forced; for `o = ⊤`, every lift has the label `⊤`. -/
theorem exists_lift_label_eq_ofOffset (hfp : restrictFace f q = some p) (hd : p.label d = ⊤) :
    ∃ Q : StageType.{u} (β + ω) m, Q.reduce hβ = q ∧ ∃ P, restrictFace f Q = some P ∧
      ∀ i : Fin P.card, (i : ℕ) = d →
        P.label i = Label.ofOffset β (provisionalOffset (β + ω) hβ q f p d) := by
  induction h : provisionalOffset (β + ω) hβ q f p d using ENat.recTopCoe with
  | top =>
    have hQ : (q.castLE (le_self_add : β ≤ β + ω)).reduce hβ = q := by
      rw [reduce_castLE, reduce_self]
    obtain ⟨P, hP, -⟩ := exists_restrictFace_reduce_eq hfp hQ
    refine ⟨_, hQ, P, hP, fun i hi ↦ ?_⟩
    rw [Label.ofOffset_top]
    by_contra hne
    have hlt : P.label i < ((β + ω : Ordinal.{u}) : Label.{u}) := (P.atStage i).resolve_right hne
    have hall : ∀ n : ℕ, ((β + n : Ordinal.{u}) : Label.{u}) ≤ P.label i := fun n ↦
      ((le_provisionalOffset_iff hfp hd).mp (h ▸ le_top)).2 _ P hQ hP i hi
    induction hx : P.label i using Label.recBotCoeTop with
    | bot => exact (WithBot.bot_lt_coe _).not_ge (hx ▸ hall 0)
    | top => exact hne hx
    | coe v =>
      rw [hx] at hlt hall
      obtain ⟨c, hc, hvc⟩ := (Ordinal.lt_add_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp
        (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt))
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
      exact hvc.not_ge (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp (hall n)))
  | coe o =>
    have hn : ForcesThreshold (β + ω) hβ q f p d o := (le_provisionalOffset_iff hfp hd).mp h.ge
    have hn1 : ¬ ForcesThreshold (β + ω) hβ q f p d (o + 1) := fun h1 ↦ by
      have := h1.le_provisionalOffset
      rw [h, Nat.cast_le] at this
      omega
    simp only [ForcesThreshold, hfp, true_and, not_forall] at hn1
    obtain ⟨Q, P, hQ, hP, i, hi, hlt⟩ := hn1
    refine ⟨Q, hQ, P, hP, fun i' hi' ↦ ?_⟩
    obtain rfl : i' = i := Fin.ext (hi'.trans hi.symm)
    rw [Label.ofOffset_natCast]
    refine le_antisymm ?_ (hn.2 Q P hQ hP i' hi')
    rw [Nat.cast_add_one, ← add_assoc] at hlt
    exact Label.lt_coe_add_one_iff.mp (not_le.mp hlt)

/-! ### Forced thresholds at twins -/

section Twins

open Finset

/-- `β + K < α` as labels for `β + ω ≤ α`. -/
private theorem coe_add_lt_of_le (hα : β + ω ≤ α) (K : ℕ) :
    ((β + K : Ordinal.{u}) : Label.{u}) < (α : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_right (natCast_lt_omega0 K) β).trans_le hα))

/-- `β + N ≤ β + K` as labels exactly when `N ≤ K`. -/
private theorem coe_add_le_coe_add_iff {N K : ℕ} :
    ((β + N : Ordinal.{u}) : Label.{u}) ≤ ((β + K : Ordinal.{u}) : Label.{u}) ↔ N ≤ K := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, add_le_add_iff_left, Nat.cast_le]

variable (hβ) in
/-- **The capped lift**: the lift of `q` to a stage `α ≥ β + ω` with the label `β + K` at every
cell labelled the formal top, for `K` at least the grade of each such cell.  Its labels are lawful
because `β + K` is self-visible at the grade of each such cell ([Kni26, Lemma 2.5.8]). -/
noncomputable def capLift (hα : β + ω ≤ α) (q : StageType.{u} β m) (K : ℕ)
    (hK : ∀ d, q.label d = ⊤ → q.toCellScheme.grade d ≤ K) : StageType.{u} α m where
  toScheme := q.toScheme
  label d := min (q.label d) ((β + K : Ordinal.{u}) : Label.{u})
  isWellFormed := q.isWellFormed
  isCoded := q.isCoded
  isLawful := q.isLawful.min_const fun d hd ↦ by
    rcases q.atStage d with h | h
    · exact absurd h ((Label.coe_le_coe_add β K).trans hd).not_gt
    · exact Label.isSelfVisible_coe_add hβ (hK d h)
  atStage _ := .inl ((min_le_right _ _).trans_lt (coe_add_lt_of_le hα K))

variable (hβ) in
/-- The label of the capped lift at a cell is the minimum of the label of `q` and `β + K`. -/
@[simp] theorem capLift_label (hα : β + ω ≤ α) (q : StageType.{u} β m) (K : ℕ)
    (hK : ∀ d, q.label d = ⊤ → q.toCellScheme.grade d ≤ K) (d : Fin q.card) :
    (capLift hβ hα q K hK).label d = min (q.label d) ((β + K : Ordinal.{u}) : Label.{u}) :=
  rfl

variable (hβ) in
/-- The capped lift reduces to `q`. -/
theorem capLift_reduce (hα : β + ω ≤ α) (q : StageType.{u} β m) (K : ℕ)
    (hK : ∀ d, q.label d = ⊤ → q.toCellScheme.grade d ≤ K) :
    (capLift hβ hα q K hK).reduce hβ = q :=
  StageType.ext rfl fun i j hij ↦ by
    obtain rfl : i = j := Fin.ext hij
    -- `i` is indexed by the reduction, so both lemmas are given their arguments explicitly
    rw [reduce_label (t := capLift hβ hα q K hK) hβ i, capLift_label hβ hα q K hK i]
    rcases q.atStage i with h | h
    · rw [min_eq_left (h.le.trans (Label.coe_le_coe_add β K)), Label.reduce_of_lt h]
    · rw [h, min_eq_right le_top]
      exact Label.reduce_of_le (Label.coe_le_coe_add β K)

/-- **Forced twins**: if `q` is legal and every lift of `q` to `α ≥ β + ω` is at least `β + N` at a
cell `s₀` labelled the formal top, then for every cell `t₀` with the scope of `s₀` in that of `t₀`
and equal grades, some cell labelled the formal top at the graded index of `t₀` is at least `β + N`
in every lift.  For `N` above the grade of `s₀`: the capped lift gives `N ≤ K` for the largest
grade `K` of a cell labelled the formal top; completeness and availability give a cell `D` of full
scope and grade `K` labelled the formal top; availability of the row of `D`, which is lawful below
`D`, names the cell `w`; and locality of every lift at `D` gives `min (Q s₀) (Q D) ≤ Q w`. -/
theorem exists_forcesThreshold_twin (hα : β + ω ≤ α) (hq : q.IsLegal) {s₀ t₀ : Fin q.card}
    (hst : q.toCellScheme.scope s₀ ⊆ q.toCellScheme.scope t₀)
    (hg : q.toCellScheme.grade s₀ = q.toCellScheme.grade t₀) (hs : q.label s₀ = ⊤) {N : ℕ}
    (hN : ForcesThreshold α hβ q (Function.Embedding.refl _) q s₀ N) :
    ∃ w, q.toCellScheme.gradedIndex w = q.toCellScheme.gradedIndex t₀ ∧ q.label w = ⊤ ∧
      ForcesThreshold α hβ q (Function.Embedding.refl _) q w N := by
  classical
  obtain ⟨w₀, hw₀, hle₀⟩ := q.isLawful.availability s₀ t₀ hst hg
  have hw₀t : q.label w₀ = ⊤ := top_le_iff.mp (hs ▸ hle₀)
  by_cases hNg : N ≤ q.toCellScheme.grade s₀
  · refine ⟨w₀, hw₀, hw₀t, forcesThreshold_of_le_grade (restrictFace_refl q) hw₀t ?_⟩
    have : q.toCellScheme.grade w₀ = q.toCellScheme.grade t₀ := congrArg Prod.snd hw₀
    omega
  push Not at hNg
  -- the largest grade `K` of a cell labelled the formal top
  set T := univ.filter fun d : Fin q.card ↦ q.label d = ⊤ with hTdef
  have hT : T.Nonempty := ⟨s₀, mem_filter.mpr ⟨mem_univ _, hs⟩⟩
  set K := T.sup fun d ↦ q.toCellScheme.grade d with hKdef
  have hK : ∀ d, q.label d = ⊤ → q.toCellScheme.grade d ≤ K := fun d hd ↦
    le_sup (f := fun d ↦ q.toCellScheme.grade d) (mem_filter.mpr ⟨mem_univ _, hd⟩)
  -- `N ≤ K`: the capped lift has `β + K` at `s₀`
  have hQ₀ := capLift_reduce hβ hα q K hK
  have hNK : N ≤ K := by
    have h := hN.2 _ _ hQ₀ (restrictFace_refl _) s₀ rfl
    rw [capLift_label, hs, min_eq_right le_top] at h
    exact coe_add_le_coe_add_iff.mp h
  -- a full-scope cell `D` of grade `K` labelled the formal top
  obtain ⟨E, hE, hEK⟩ := exists_mem_eq_sup T hT fun d ↦ q.toCellScheme.grade d
  have hEK' : K = q.toCellScheme.grade E := hEK
  have hEt : q.label E = ⊤ := (mem_filter.mp hE).2
  obtain ⟨D', hD'⟩ := hq.isComplete ((univ : Finset (Fin m)), K)
    ⟨q.univ_mem_faces, by omega, by
      change K ≤ #(Finset.univ : Finset (Fin m))
      rw [Finset.card_univ, Fintype.card_fin, hEK']; exact q.grade_le E⟩
  have hD's : q.toCellScheme.scope D' = Finset.univ := congrArg Prod.fst hD'
  have hD'g : q.toCellScheme.grade D' = K := congrArg Prod.snd hD'
  obtain ⟨D, hD, hED⟩ := q.isLawful.availability E D' (hD's ▸ subset_univ _) (by
    rw [hD'g, hEK'])
  have hDt : q.label D = ⊤ := top_le_iff.mp (hEt ▸ hED)
  have hDi : q.toCellScheme.gradedIndex D = ((univ : Finset (Fin m)), K) := hD.trans hD'
  have hDg : q.toCellScheme.grade D = K := congrArg Prod.snd hDi
  have hbelow : ∀ d, q.toCellScheme.grade d ≤ K →
      d ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex D) := fun d hd ↦ by
    rw [CellScheme.mem_below, hDi]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, hd⟩
  have hs₀D := hbelow s₀ (by omega)
  have ht₀D := hbelow t₀ (by omega)
  -- the availability witness in the row of `D`
  obtain ⟨u, hu, hrow⟩ := (CellScheme.Rows.isLawfulBelow_iff.mp (hq.isConsistent D)).availability
    ⟨s₀, hs₀D⟩ ⟨t₀, ht₀D⟩ hst hg
  have hu' : q.toCellScheme.gradedIndex u.1 = q.toCellScheme.gradedIndex t₀ := hu
  have hug : q.toCellScheme.grade u.1 = q.toCellScheme.grade s₀ :=
    (congrArg Prod.snd hu').trans hg.symm
  have hforce : ForcesThreshold α hβ q (Function.Embedding.refl _) q u.1 N := by
    refine ⟨restrictFace_refl q, fun Q P hQ hP i hi ↦ ?_⟩
    obtain rfl : P = Q := Option.some_injective _ (hP.symm.trans (restrictFace_refl Q))
    subst hQ
    obtain rfl : i = u.1 := Fin.ext hi
    have h₁ := hN.2 P P rfl (restrictFace_refl P) s₀ rfl
    have h₂ := (forcesThreshold_of_le_grade (n := N) (restrictFace_refl _) hDt (by omega)).2
      P P rfl (restrictFace_refl P) D rfl
    have h₃ := (P.isLawful.locality D).le_of_le (d := ⟨s₀, hs₀D⟩) (d' := u) hrow hug.le
    exact (le_min h₁ h₂).trans (h₃.trans (min_le_left _ _))
  refine ⟨u.1, hu', ?_, hforce⟩
  have h := hforce.2 _ _ hQ₀ (restrictFace_refl _) u.1 rfl
  rw [capLift_label] at h
  rcases q.atStage u.1 with hlt | htop
  · exact absurd ((Label.coe_le_coe_add β N).trans (h.trans (min_le_left _ _))) (not_le.mpr hlt)
  · exact htop

/-- **Forced twins over a face**: if a legal `q` restricts to `p` along `f` and `(q, f)` forces `N`
at a cell `s₀` of `p` labelled the formal top, then `(q, f)` forces `N` at some cell labelled the
formal top at the graded index of every `t₀` with the scope of `s₀` in that of `t₀` and equal
grades.  The cell given by `exists_forcesThreshold_twin` in `q` lies in the face spanned by `f`. -/
theorem exists_forcesThreshold_twin_face (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hp : restrictFace f q = some p) {s₀ t₀ : Fin p.card}
    (hst : p.toCellScheme.scope s₀ ⊆ p.toCellScheme.scope t₀)
    (hg : p.toCellScheme.grade s₀ = p.toCellScheme.grade t₀) (hs : p.label s₀ = ⊤) {N : ℕ}
    (hN : ForcesThreshold α hβ q f p s₀ N) :
    ∃ w, p.toCellScheme.gradedIndex w = p.toCellScheme.gradedIndex t₀ ∧ p.label w = ⊤ ∧
      ForcesThreshold α hβ q f p w N := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff q f).mp hp
  have key (i : Fin (q.comap f hf).card) (n : ℕ) :
      ForcesThreshold α hβ q f (q.comap f hf) i n ↔
        ForcesThreshold α hβ q (Function.Embedding.refl _) q (q.cellMap f i) n := by
    have h := ForcesThreshold.trans_comap_iff (α := α) (hβ := hβ) (n := n)
      (restrictFace_refl q) hf i
    rwa [Function.Embedding.trans_refl] at h
  have hst' : q.toCellScheme.scope (q.cellMap f s₀) ⊆ q.toCellScheme.scope (q.cellMap f t₀) := by
    rw [← q.toScheme.map_comap_scope f s₀, ← q.toScheme.map_comap_scope f t₀]
    exact map_subset_map.mpr hst
  obtain ⟨w', hw', hw't, hw'f⟩ := exists_forcesThreshold_twin hα hq hst' hg hs ((key s₀ N).mp hN)
  have hvis : w' ∈ Set.range (q.cellMap f) := by
    rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells, show q.toCellScheme.scope w' =
      q.toCellScheme.scope (q.cellMap f t₀) from congrArg Prod.fst hw']
    exact Scheme.mem_visibleCells.mp (q.toScheme.cellMap_mem f t₀)
  obtain ⟨w, rfl⟩ := hvis
  refine ⟨w, ?_, hw't, (key w N).mpr hw'f⟩
  -- the graded index of `comap f hf` is that of the underlying scheme `q.toScheme.comap f`
  change (q.toScheme.comap f).toCellScheme.gradedIndex w =
    (q.toScheme.comap f).toCellScheme.gradedIndex t₀
  have h := hw'
  rw [← q.toScheme.map_comap_gradedIndex f w, ← q.toScheme.map_comap_gradedIndex f t₀] at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext (map_injective f h₁) h₂

end Twins

end StageType

end VaughtConjecture

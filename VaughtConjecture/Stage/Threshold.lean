/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.ENat.Lattice
import VaughtConjecture.Stage.Basic

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

end StageType

end VaughtConjecture

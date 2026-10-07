/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Order
import VaughtConjecture.Realization.Basic
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Hull
import VaughtConjecture.Realization.Model
import VaughtConjecture.Scheme.Row
import VaughtConjecture.Stage.Legal
import VaughtConjecture.Stage.Cap

/-!
# Terminal models, top grade, admissible top supports, and rigid cores

Roadmap, Layer 4 (terminal classification: rigid finite core, eventual top grade, hollow
unbounded growth; the working definitions of admissible top support and rigid core; top-grade
growth defined directly through covers, not through characteristic arity); semantic contract,
item 8 (a rigid core is a top-support condition, not automorphism rigidity; the grade-zero case is
handled by the empty rigid core).

**Terminality.**  A realization `R` at the block stage `λ_ξ` (`blockStage ξ`) is **terminal at
`ξ`** (`Realization.IsTerminalAt`) when no model at the next block stage `λ_{ξ+1}` on the same
carrier has `R` as its stage reduction to `λ_ξ`.  Equivalently, no model at any stage `β > λ_ξ`
that is zero or a limit reduces to `R` (`isTerminalAt_iff_forall_lt`): such a `β` is at least
`λ_{ξ+1}`, and a model at `β` reduces to a model at `λ_{ξ+1}` (`IsModel.reduce`) with the same
reduction to `λ_ξ` (`Realization.reduce_reduce`).  If no model at `λ_{ξ+1}` on the carrier of a
base structure `M` is an expansion of `M`, every expansion of `M` at `λ_ξ` is terminal
(`IsExpansionOf.isTerminalAt`): a model at `λ_{ξ+1}` reducing to it would have the base reduct
`M`.  No uniqueness of expansions is used.

**Top grade.**  The **top grade** of a stage type (`StageType.topGrade`) is the largest grade of a
cell labelled `⊤`, and `0` if there is none; it is `0` exactly for the top-free types
(`StageType.topGrade_eq_zero_iff`), since grades are positive, and it does not increase along
face maps (`StageType.topGrade_le_of_restrictFace`).  The **top-grade supremum** of a realization
(`Realization.topGradeSup`, in `ℕ∞`) is the supremum of the top grades of its occurrences.  Under
exact consistency the top grade is monotone along the occurrences ordered by inclusion of
supports (`Realization.Occurrence.topGrade_mono`), and under covering the occurrences containing
any finite set are directed (`Realization.IsCovering.directedOn_setOf_subset_support`), so the
supremum is the eventual value along the covers of any finite set
(`topGradeSup_eq_iSup_subset_support`); when it is a natural number `K`, the top grade is `K` on
every occurrence containing some fixed one (`exists_forall_le_topGrade_eq`).  Bounded growth is
`topGradeSup = K` for a natural number `K`; unbounded growth is `topGradeSup = ⊤`.

**Admissible top supports and rigid cores.**  The cells of a stage type are indexed by
`Fin t.card`, and labels of two types on the same scheme are compared at equal positions.  A set
`H` of cells of `t` is an **admissible top support** (`StageType.IsAdmissibleTopSupport`) when some
legal stage type `t'` on the scheme of `t` agrees with `t` at every cell not labelled `⊤` in `t`,
is `⊤` exactly on `H`, and has proper labels (ordinals below the stage) at the other top cells of
`t`.  So `H` consists of top cells of `t` (`IsAdmissibleTopSupport.subset`), and the top cells of a
legal `t` form an admissible top support (`isAdmissibleTopSupport_top`).  For a face embedding
`e : Fin k ↪ Fin n`, the core along `e` is **rigid** in `t` (`StageType.IsRigidCoreIn`) when every
admissible top support containing the top cells supported on the core (the cells visible through
`e`, `Scheme.visibleCells`, the range of the cell map of the face) contains every top cell.
Rigidity concerns admissible top supports, not automorphisms.  A larger core is rigid when a
smaller one is (`IsRigidCoreIn.mono`), a top-free type has every core rigid
(`isRigidCoreIn_of_isTopFree`).  At a limit stage, a core on which no top cell is supported is not
rigid in a legal type that is not top-free (`not_isRigidCoreIn_of_forall_visibleCells`): the type
capped at a cap self-visible at the arity, below the stage and above every proper label
(`StageType.cap`, lawful by [Kni26, Lemma 2.5.8]), keeps the other labels and lowers every top
label to the cap, so the empty set is an admissible top support.  In particular a top-free face is
not a rigid core of a legal type that is not top-free
(`not_isRigidCoreIn_of_restrictFace_isTopFree`), and the empty core is rigid in a legal type
exactly when the type is top-free (`isRigidCoreIn_empty_iff_isTopFree`).

A tuple `c` is a **globally rigid core** of `R` (`Realization.IsGloballyRigidCore`) when the core
along `e` is rigid in `t` for every cover `x` of a stage type `t` in `R` and every `e` with
`x ∘ e = c`.  Every tuple containing the points of an injective globally rigid core is one
(`IsGloballyRigidCore.mono`), so
a covering realization (every injective tuple is a face of a cover) has a globally rigid core
among the injectively enumerated finite sets exactly when it has one among the covers.  For a
model at a limit stage, the top-grade supremum is `0` exactly when every actual type
is top-free (`topGradeSup_eq_zero_iff`), exactly when the empty tuple is a globally rigid core
(`IsModel.isGloballyRigidCore_empty_iff`).

Everything here is unconditional.  What uses it is still to be proved: the classification of
terminal models into the rigid-core, residual, and hollow kinds (which needs the continuation
criterion, output 3 of higher-stage reconstruction, and only its sufficiency direction), the
comparisons for each kind (from (R1), (R2), (R3) of the table of Layer 3), and the countability of
the successor losses.  Nothing here concerns uniqueness or coherence of expansions, global
termination, the converse of output 3, a canonical choice of kind, or characteristic arity.
Hollowness is deliberately not defined here: the anchor predicate is still to be transcribed, and
its stable-label form is to be a theorem for models (semantic contract, item 8).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

variable {α : Ordinal.{u}} {M : Type v} {n m k : ℕ}

/-! ### Terminality -/

namespace Realization

/-- A realization `R` at the block stage `λ_ξ` is **terminal at `ξ`** when no model at the next
block stage `λ_{ξ+1}` on the same carrier has `R` as its stage reduction to `λ_ξ`. -/
def IsTerminalAt (ξ : Ordinal.{u}) (R : Realization.{u, v} (blockStage ξ) M) : Prop :=
  ∀ R' : Realization.{u, v} (blockStage (ξ + 1)) M, R'.IsModel →
    R'.reduce (isSuccPrelimit_blockStage ξ) ≠ R

/-- A stage above a block stage that is zero or a limit is at least the next block stage. -/
private theorem blockStage_add_one_le {ξ β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    (h : blockStage ξ < β) : blockStage (ξ + 1) ≤ β := by
  rw [blockStage_add_one]
  refine (Ordinal.add_le_iff Ordinal.omega0_ne_zero).mpr fun d hd ↦ ?_
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hd
  exact hβ.add_natCast_lt h n

/-- **Terminality against all higher stages**: `R` is terminal at `ξ` exactly when no model at any
stage `β > λ_ξ` that is zero or a limit reduces to `R`. -/
theorem isTerminalAt_iff_forall_lt {ξ : Ordinal.{u}} {R : Realization.{u, v} (blockStage ξ) M} :
    R.IsTerminalAt ξ ↔ ∀ ⦃β : Ordinal.{u}⦄, Order.IsSuccPrelimit β → blockStage ξ < β →
      ∀ R' : Realization.{u, v} β M, R'.IsModel →
        R'.reduce (isSuccPrelimit_blockStage ξ) ≠ R := by
  refine ⟨fun h β hβ hlt R' hR' ↦ ?_, fun h ↦ h (isSuccPrelimit_blockStage (ξ + 1))
    (blockStage_lt_blockStage_add_one ξ)⟩
  have hle := blockStage_add_one_le hβ hlt
  rw [← R'.reduce_reduce (isSuccPrelimit_blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ)
    (blockStage_lt_blockStage_add_one ξ).le]
  exact h _ (hR'.reduce hβ (isSuccLimit_blockStage (ξ + 1)) hle)

/-- **Expansions are terminal when the next block has none**: if no model at `λ_{ξ+1}` on the
carrier of the base structure `M` is an expansion of `M`, every expansion of `M` at `λ_ξ` is
terminal at `ξ`.  A model at `λ_{ξ+1}` reducing to it would have base reduct `M`
(`Realization.reduce_reduce`). -/
theorem IsExpansionOf.isTerminalAt [baseLanguage.{u}.Structure M] {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsExpansionOf)
    (h : IsEmpty (ModelExpansion M (blockStage (ξ + 1)))) : R.IsTerminalAt ξ := by
  intro R' hR' heq
  refine h.false ⟨R', hR', ?_⟩
  rw [← R'.reduce_reduce (isSuccPrelimit_blockStage ξ) Ordinal.isSuccLimit_omega0.isSuccPrelimit
    (omega0_le_blockStage ξ), heq]
  exact hR.toStructure_reduce

end Realization

/-! ### Top grade -/

namespace StageType

variable {t : StageType.{u} α n}

open Classical in
/-- The **top grade** of a stage type: the largest grade of a cell labelled `⊤`, and `0` if there
is none. -/
noncomputable def topGrade (t : StageType.{u} α n) : ℕ :=
  ({d | t.label d = ⊤} : Finset (Fin t.card)).sup t.toCellScheme.grade

/-- A cell labelled `⊤` has grade at most the top grade. -/
theorem grade_le_topGrade {d : Fin t.card} (hd : t.label d = ⊤) :
    t.toCellScheme.grade d ≤ t.topGrade := by
  classical
  exact le_sup (f := t.toCellScheme.grade) (by simpa using hd)

/-- The top grade is at most `K` exactly when every cell labelled `⊤` has grade at most `K`. -/
theorem topGrade_le_iff {K : ℕ} :
    t.topGrade ≤ K ↔ ∀ d, t.label d = ⊤ → t.toCellScheme.grade d ≤ K := by
  classical
  simp [topGrade]

/-- **The top grade is `0` exactly for top-free types**, since grades are positive. -/
theorem topGrade_eq_zero_iff : t.topGrade = 0 ↔ t.IsTopFree := by
  rw [← Nat.le_zero, topGrade_le_iff]
  exact forall_congr' fun d ↦ ⟨fun h hd ↦ (t.isWellFormed.isWellFormed.grade_pos d).ne'
    (Nat.le_zero.mp (h hd)), fun h hd ↦ absurd hd h⟩

/-- **The top grade does not increase along face maps.** -/
theorem topGrade_le_of_restrictFace {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    (h : restrictFace f t = some p) : p.topGrade ≤ t.topGrade := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp h
  exact topGrade_le_iff.mpr fun i hi ↦ grade_le_topGrade (t := t) hi

end StageType

/-! ### The top-grade supremum -/

namespace Realization

variable {R : Realization.{u, v} α M}

/-- The **top-grade supremum** of a realization: the supremum of the top grades of its
occurrences, in `ℕ∞`.  Bounded growth is a natural number value; unbounded growth is `⊤`. -/
noncomputable def topGradeSup (R : Realization.{u, v} α M) : ℕ∞ :=
  ⨆ x : R.Occurrence, (x.type.topGrade : ℕ∞)

/-- The top grade of an occurrence is at most the top-grade supremum. -/
theorem Occurrence.topGrade_le_topGradeSup (x : R.Occurrence) :
    (x.type.topGrade : ℕ∞) ≤ R.topGradeSup :=
  le_iSup (fun y : R.Occurrence ↦ (y.type.topGrade : ℕ∞)) x

/-- Under exact consistency the top grade is monotone along inclusion of supports. -/
theorem Occurrence.topGrade_mono (hR : R.IsConsistent) {x y : R.Occurrence} (h : x ≤ y) :
    x.type.topGrade ≤ y.type.topGrade := by
  obtain ⟨f, -, hf⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp h
  exact StageType.topGrade_le_of_restrictFace hf

/-- **The top-grade supremum is the eventual value along covers**: under exact consistency and
covering, it is the supremum over the occurrences containing any given finite set. -/
theorem topGradeSup_eq_iSup_subset_support (hR : R.IsConsistent) (hc : R.IsCovering)
    (F : Finset M) :
    R.topGradeSup = ⨆ x : {x : R.Occurrence // F ⊆ x.support}, (x.1.type.topGrade : ℕ∞) := by
  classical
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun x ↦ x.1.topGrade_le_topGradeSup)
  obtain ⟨z, hz⟩ := hc.exists_subset_support (F ∪ x.support)
  refine le_iSup_of_le (⟨z, subset_union_left.trans hz⟩ : {x : R.Occurrence // F ⊆ x.support}) ?_
  exact Nat.cast_le.mpr (Occurrence.topGrade_mono hR (subset_union_right.trans hz))

/-- **Bounded growth is eventually constant**: if the top-grade supremum is a natural number `K`,
then under exact consistency and covering every occurrence containing some fixed occurrence has
top grade `K`. -/
theorem exists_forall_le_topGrade_eq (hR : R.IsConsistent) (hc : R.IsCovering) {K : ℕ}
    (h : R.topGradeSup = K) : ∃ x : R.Occurrence, ∀ y, x ≤ y → y.type.topGrade = K := by
  have := hc.nonempty_occurrence
  obtain ⟨x, hx⟩ := ENat.exists_eq_iSup_of_lt_top
    (f := fun y : R.Occurrence ↦ (y.type.topGrade : ℕ∞))
    (show R.topGradeSup < ⊤ from h ▸ ENat.natCast_lt_top K)
  have hxK : x.type.topGrade = K := by exact_mod_cast hx.trans h
  refine ⟨x, fun y hy ↦ le_antisymm ?_ (hxK ▸ Occurrence.topGrade_mono hR hy)⟩
  exact_mod_cast h ▸ y.topGrade_le_topGradeSup

/-- **Top-grade supremum zero**: the top-grade supremum is `0` exactly when every actual type is
top-free. -/
theorem topGradeSup_eq_zero_iff : R.topGradeSup = 0 ↔ ∀ x : R.Occurrence, x.type.IsTopFree := by
  simp only [topGradeSup, ENat.iSup_eq_zero, Nat.cast_eq_zero, StageType.topGrade_eq_zero_iff]

end Realization

/-! ### Admissible top supports and rigid cores -/

namespace StageType

variable {t : StageType.{u} α n}

variable (t) in
/-- A set `H` of cells of `t` is an **admissible top support** when some legal stage type `t'` on
the scheme of `t` agrees with `t` at every cell not labelled `⊤` in `t`, is `⊤` exactly on `H`, and
has proper labels at the other top cells of `t`.  Cells are compared at equal positions. -/
def IsAdmissibleTopSupport (H : Set (Fin t.card)) : Prop :=
  ∃ t' : StageType.{u} α n, t'.IsLegal ∧ t'.toScheme = t.toScheme ∧
    ∀ (i : Fin t'.card) (j : Fin t.card), (i : ℕ) = j →
      (t.label j ≠ ⊤ → t'.label i = t.label j) ∧ (t'.label i = ⊤ ↔ j ∈ H) ∧
        (t.label j = ⊤ → j ∉ H → (t'.label i).IsProper)

/-- An admissible top support consists of top cells. -/
theorem IsAdmissibleTopSupport.subset {H : Set (Fin t.card)} (h : t.IsAdmissibleTopSupport H) :
    H ⊆ {d | t.label d = ⊤} := by
  obtain ⟨t', -, hs, h'⟩ := h
  intro d hd
  by_contra hne
  have hc : t'.card = t.card := congrArg Scheme.card hs
  obtain ⟨hagree, htop, -⟩ := h' (Fin.cast hc.symm d) d rfl
  exact hne ((hagree hne).symm.trans ((htop).mpr hd))

/-- The top cells of a legal stage type form an admissible top support, witnessed by the type. -/
theorem isAdmissibleTopSupport_top (ht : t.IsLegal) :
    t.IsAdmissibleTopSupport {d | t.label d = ⊤} := by
  refine ⟨t, ht, rfl, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := Fin.ext hij
  exact ⟨fun _ ↦ rfl, Iff.rfl, fun h h' ↦ absurd h h'⟩

variable (t) in
/-- The core along a face embedding `e` is **rigid** in `t` when every admissible top support
containing the top cells supported on the core (the cells visible through `e`) contains every top
cell. -/
def IsRigidCoreIn (e : Fin k ↪ Fin n) : Prop :=
  ∀ H : Set (Fin t.card), t.IsAdmissibleTopSupport H →
    (∀ d ∈ t.visibleCells e, t.label d = ⊤ → d ∈ H) → ∀ d, t.label d = ⊤ → d ∈ H

/-- **A larger core is rigid** when a smaller one is: more cells are supported on it. -/
theorem IsRigidCoreIn.mono {e : Fin k ↪ Fin n} {e' : Fin m ↪ Fin n} (h : t.IsRigidCoreIn e)
    (he : Set.range e ⊆ Set.range e') : t.IsRigidCoreIn e' :=
  fun H hH hcore ↦ h H hH fun d hd ↦
    hcore d (Scheme.mem_visibleCells.mpr ((Scheme.mem_visibleCells.mp hd).trans he))

/-- In a top-free stage type every core is rigid. -/
theorem isRigidCoreIn_of_isTopFree (ht : t.IsTopFree) (e : Fin k ↪ Fin n) : t.IsRigidCoreIn e :=
  fun _ _ _ d hd ↦ absurd hd (ht d)

/-- **A core carrying no top is not rigid in a type with a top**, at a limit stage: if a legal `t`
is not top-free and no top cell of `t` is supported on the core along `e`, the core is not rigid in
`t`.  The type capped at an ordinal below the stage, self-visible at the arity and above every
proper label (`cap`, lawful by [Kni26, Lemma 2.5.8]), lowers every top label to a proper one,
keeping the others: the empty set is an admissible top support, it contains the top cells
supported on the core, of which there are none, and it misses a top cell of `t`. -/
theorem not_isRigidCoreIn_of_forall_visibleCells (hα : Order.IsSuccLimit α) (ht : t.IsLegal)
    {e : Fin k ↪ Fin n} (hvis : ∀ d ∈ t.visibleCells e, t.label d ≠ ⊤) (ht' : ¬ t.IsTopFree) :
    ¬ t.IsRigidCoreIn e := by
  intro hrig
  obtain ⟨o, hoα, ho⟩ := t.exists_label_le hα.bot_lt
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit hoα n
  have hoc' : (o : Label.{u}) < c := by exact_mod_cast hoc
  have hadm : t.IsAdmissibleTopSupport ∅ := by
    refine ⟨t.cap c hc hcα, ht, rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    refine ⟨fun hne ↦ min_eq_left ((ho i hne).trans hoc'.le), ?_, fun hi _ ↦ ?_⟩
    · exact iff_of_false (isTopFree_cap i) (Set.notMem_empty i)
    · rw [cap_label (t := t) i, hi, min_eq_right le_top]
      exact isProper_coe c
  exact ht' fun d hd ↦ Set.notMem_empty d
    (hrig ∅ hadm (fun d' hd' htop ↦ absurd htop (hvis d' hd')) d hd)

/-- **A top-free core is not rigid in a type with a top**, at a limit stage: if a legal `D` has a
top-free face `p` along `e` and is not top-free, the core along `e` is not rigid in `D`.  The top
cells supported on the core are cells of the face, so there are none
(`not_isRigidCoreIn_of_forall_visibleCells`). -/
theorem not_isRigidCoreIn_of_restrictFace_isTopFree (hα : Order.IsSuccLimit α)
    {D : StageType.{u} α m} (hD : D.IsLegal) {e : Fin n ↪ Fin m} {p : StageType.{u} α n}
    (he : restrictFace e D = some p) (hp : p.IsTopFree) (hD' : ¬ D.IsTopFree) :
    ¬ D.IsRigidCoreIn e := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D e).mp he
  refine not_isRigidCoreIn_of_forall_visibleCells hα hD (fun y hy ↦ ?_) hD'
  obtain ⟨i, rfl⟩ : y ∈ Set.range (D.cellMap e) := by
    rw [Scheme.range_cellMap]
    exact hy
  exact hp i

/-- **The empty core is rigid exactly in the top-free types**: at a limit stage, the empty core is
rigid in a legal stage type exactly when the type is top-free.  No cell is supported on the empty
core, so otherwise the core is not rigid (`not_isRigidCoreIn_of_forall_visibleCells`). -/
theorem isRigidCoreIn_empty_iff_isTopFree (hα : Order.IsSuccLimit α) (ht : t.IsLegal)
    (e : Fin 0 ↪ Fin n) : t.IsRigidCoreIn e ↔ t.IsTopFree := by
  refine ⟨fun h ↦ by_contra fun ht' ↦ not_isRigidCoreIn_of_forall_visibleCells hα ht
    (fun d hd _ ↦ ?_) ht' h, fun h ↦ isRigidCoreIn_of_isTopFree h e⟩
  -- no cell is supported on the empty core: its scope would be empty
  have hs : t.toCellScheme.scope d = ∅ := by
    rw [Scheme.mem_visibleCells, Set.range_eq_empty] at hd
    exact coe_eq_empty.mp (Set.subset_empty_iff.mp hd)
  have hle := t.isWellFormed.isWellFormed.grade_le_card d
  have hpos := t.isWellFormed.isWellFormed.grade_pos d
  rw [hs, card_empty] at hle
  omega

end StageType

/-! ### Globally rigid cores -/

namespace Realization

variable {R : Realization.{u, v} α M}

variable (R) in
/-- A tuple `c` is a **globally rigid core** of `R` when, for every cover `x` of a stage type `t`
in `R` and every face embedding `e` with `x ∘ e = c`, the core along `e` is rigid in `t`. -/
def IsGloballyRigidCore (c : Fin k → M) : Prop :=
  ∀ ⦃m : ℕ⦄ (t : StageType.{u} α m) (x : Fin m → M) (e : Fin k ↪ Fin m), R.Covers t x →
    x ∘ e = c → t.IsRigidCoreIn e

/-- **A larger core is globally rigid**: every tuple containing the points of an injective
globally rigid core is a globally rigid core.  So a covering realization (every injective tuple
is a face of a cover) has a globally rigid core among its injectively enumerated finite sets
exactly when it has one among its covers. -/
theorem IsGloballyRigidCore.mono {c : Fin k → M} {c' : Fin m → M}
    (h : R.IsGloballyRigidCore c) (hc : Function.Injective c) (hcc : Set.range c ⊆ Set.range c') :
    R.IsGloballyRigidCore c' := by
  intro n t x e' hx hxe'
  have hmem (i : Fin k) : ∃ j, x (e' j) = c i := by
    obtain ⟨j, hj⟩ := hcc ⟨i, rfl⟩
    exact ⟨j, (congrFun hxe' j).trans hj⟩
  choose j hj using hmem
  have hxc : x ∘ (e' ∘ j) = c := funext hj
  have hinj : Function.Injective (e' ∘ j) := Function.Injective.of_comp (f := x) (hxc ▸ hc)
  refine (h t x ⟨_, hinj⟩ hx hxc).mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨j i, rfl⟩

/-- **Top-free realizations**: if every actual type is top-free, every tuple is a globally rigid
core. -/
theorem isGloballyRigidCore_of_forall_isTopFree (h : ∀ x : R.Occurrence, x.type.IsTopFree)
    (c : Fin k → M) : R.IsGloballyRigidCore c :=
  fun _ t x e hx _ ↦
    StageType.isRigidCoreIn_of_isTopFree (h ⟨_, ⟨x, hx.injective⟩, t, hx.eval_eq⟩) e

/-- **The empty core of a model**: for a model at a limit stage, the empty tuple is a globally
rigid core exactly when the top-grade supremum is `0`, that is, exactly when every actual type is
top-free (`topGradeSup_eq_zero_iff`). -/
theorem IsModel.isGloballyRigidCore_empty_iff (hR : R.IsModel) (hα : Order.IsSuccLimit α) :
    R.IsGloballyRigidCore ![] ↔ R.topGradeSup = 0 := by
  rw [topGradeSup_eq_zero_iff]
  refine ⟨fun h x ↦ ?_, fun h ↦ isGloballyRigidCore_of_forall_isTopFree h _⟩
  refine (StageType.isRigidCoreIn_empty_iff_isTopFree hα (hR.isLegal _ _ x.eval_tuple)
    Function.Embedding.ofIsEmpty).mp ?_
  exact h x.type x.tuple _ (covers_of_eval _ x.eval_tuple) (funext fun i ↦ i.elim0)

end Realization

end VaughtConjecture

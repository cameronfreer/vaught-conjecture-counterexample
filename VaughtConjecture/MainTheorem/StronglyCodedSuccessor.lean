/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.StronglyCodedCalibratedContexts

/-!
# The successor in the strongly coded receiving class, and strongly coded terminality

Roadmap, Layer 4 (output 3 of higher-stage reconstruction, and the terminal classification: hollow
unbounded growth) and Correspondence, item 1 (the strongly coded legal stage types).

**The class.**  A realization `R` at a stage `α` is in the **strongly coded receiving class**
(`Realization.IsStronglyCodedReceiving`) when it is exactly consistent, covering, with legal types,
with strongly coded types (the rows of every actual type are strongly coded) and with finite-cut
receiving for the cofaces with strongly coded rows
(`Realization.HasFiniteCutReceivingIn`).  The class is stated at every stage; it is used at the
block stages `λ_ξ` and `λ_{ξ+1}`.  It is not the class of models: saturation, the bottom pattern,
uniformity and dominance are not among its clauses, and receiving is required only for strongly
coded cofaces.

**The successor.**  For `R` in the class at `λ_ξ`, stable lawfulness holds
(`Realization.isStablyLawful_of_hasLegalTypes`), so the stable candidate
`R.stableCandidate hR.isStablyLawful` at `λ_{ξ+1}` is defined, and it reduces literally to `R`
(`Realization.stableCandidate_reduce`: `(R.stableCandidate _).reduce
(isSuccPrelimit_blockStage ξ) = R`, the reduction of `Realization.IsTerminalAt`).

* `Realization.StronglyCodedSuccessorTarget ξ M`: for `R` in the class at `λ_ξ`, not cover-hollow
  and with top-grade supremum `⊤`, the stable candidate is in the class at `λ_{ξ+1}` and reduces
  literally to `R`.
* `Realization.StronglyCodedEmptyRootTarget ξ M`: the clause of strongly coded finite-cut receiving
  of the candidate over the occurrences on no points.  (R4) concerns positive roots only; over the
  empty root, a one-point donor is combined with the type of an occurrence of positive arity by
  the strongly coded amalgam over the empty face.  This needs a point of the carrier.

**Terminality in the class.**  `Realization.IsStronglyCodedTerminalAt ξ R`: `R` is in the class at
`λ_ξ` and no realization in the class at `λ_{ξ+1}` reduces literally to `R`.  This is not
`Realization.IsTerminalAt` (which quantifies over models at `λ_{ξ+1}`), nor
`Realization.IsReceivingTerminalAt` (which quantifies over receiving models at `λ_{ξ+1}`).

* `Realization.StronglyCodedTerminalHollowTarget ξ M`: a realization terminal in the class at `ξ`
  with top-grade supremum `⊤` is cover-hollow.

**Proofs** (native constructions of this repository; no correspondence with [AFK26] is claimed).
The argument is that of `Realization.isModel_stableCandidate` and
`Realization.hasFiniteCutReceiving_stableCandidate`, with the conclusion membership in the class
instead of modelhood, and each use of modelhood replaced:

* the point of the carrier (`Realization.IsModel.nonempty`) comes from unbounded growth
  (`Realization.nonempty_of_topGradeSup_eq_top`: a cell labelled `⊤` of positive grade has a
  nonempty scope);
* exact consistency, covering and legal types of the candidate come from those fields of the class
  (as for a model); strong coding of its types holds because the candidate keeps the schemes;
* (R4) over positive roots, a hypothesis for models (`StableCappedReceiving`), is proved for
  strongly coded cofaces (`Realization.stablyReceivesAt_of_isStronglyCoded`), read as receiving in
  `Realization.IsStronglyCodedReceiving.realizesOver_stableCandidate_of_pos`;
* the amalgam over the empty face (`StageType.HasNonemptyCofaceInstances.exists_amalgam_empty`) is
  replaced by the strongly coded amalgam
  (`StageType.HasStronglyCodedCofaceInstances.exists_amalgam_empty`), whose output has strongly
  coded rows, so that it is received by the positive-root step
  (`Realization.realizesOver_of_arity_eq_zero`);
* the uniformity and dominance instances are not used: they are not clauses of the class.

The results are `Realization.isStronglyCodedReceiving_stableCandidate`,
`Realization.IsStronglyCodedTerminalAt.isCoverHollow` and the three targets
`Realization.stronglyCodedSuccessorTarget`, `Realization.stronglyCodedEmptyRootTarget` and
`Realization.stronglyCodedTerminalHollowTarget`.  Bounded growth, rigid cores, the residual and
hollow comparisons, and the relation of this terminality to models are not addressed.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType

namespace Realization

/-! ### The strongly coded receiving class -/

section Class

variable {α : Ordinal.{u}} {M : Type v}

/-- A realization is in the **strongly coded receiving class** when it is exactly consistent,
covering, with legal types, with strongly coded types and with finite-cut receiving for the
cofaces with strongly coded rows. -/
structure IsStronglyCodedReceiving (R : Realization.{u, v} α M) : Prop where
  /-- Exact consistency. -/
  isConsistent : R.IsConsistent
  /-- Covering. -/
  isCovering : R.IsCovering
  /-- Legal types. -/
  hasLegalTypes : R.HasLegalTypes
  /-- Strongly coded types: the rows of every actual type are strongly coded. -/
  isStronglyCoded : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
    p.rows.IsStronglyCoded
  /-- Finite-cut receiving for the cofaces with strongly coded rows. -/
  receiving : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded

/-- A realization in the strongly coded receiving class at a block stage is stably lawful
(`Realization.isStablyLawful_of_hasLegalTypes`). -/
theorem IsStronglyCodedReceiving.isStablyLawful {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving) :
    R.IsStablyLawful :=
  isStablyLawful_of_hasLegalTypes hR.isConsistent hR.isCovering hR.hasLegalTypes

/-- A realization at `λ_ξ` is **terminal in the strongly coded receiving class at `ξ`** when it is
in the class and no realization in the class at `λ_{ξ+1}` on the same carrier has it as its stage
reduction to `λ_ξ`. -/
def IsStronglyCodedTerminalAt (ξ : Ordinal.{u}) (R : Realization.{u, v} (blockStage ξ) M) :
    Prop :=
  R.IsStronglyCodedReceiving ∧ ¬ ∃ R' : Realization.{u, v} (blockStage (ξ + 1)) M,
    R'.IsStronglyCodedReceiving ∧ R'.reduce (isSuccPrelimit_blockStage ξ) = R

end Class

/-! ### Targets -/

section Targets

variable (ξ : Ordinal.{u}) (M : Type v)

/-- **Target: the successor in the strongly coded receiving class**.  For `R` in the class at
`λ_ξ`, not cover-hollow and with top-grade supremum `⊤`, the stable candidate
`R.stableCandidate hR.isStablyLawful` is in the class at `λ_{ξ+1}`, and its stage reduction to
`λ_ξ` is `R` literally. -/
def StronglyCodedSuccessorTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsStronglyCodedReceiving),
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      (R.stableCandidate hR.isStablyLawful).IsStronglyCodedReceiving ∧
        (R.stableCandidate hR.isStablyLawful).reduce (isSuccPrelimit_blockStage ξ) = R

/-- **Target: strongly coded receiving of the successor over the empty root**.  For `R` in the
class at `λ_ξ`, not cover-hollow and with top-grade supremum `⊤`, over every occurrence of the
stable candidate on no points, every coface of its type with strongly coded rows (a strongly coded
legal stage type on one point) and every permitted cutoff at `λ_{ξ+1}`, the candidate receives
the coface. -/
def StronglyCodedEmptyRootTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsStronglyCodedReceiving),
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, x.arity = 0 →
        ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded → ∀ c : Label.{u},
          IsPermittedCutoff (blockStage (ξ + 1)) c →
            (R.stableCandidate hR.isStablyLawful).RealizesOver x.tuple (receivingFamily D c)

/-- **Target: terminality in the strongly coded receiving class with unbounded growth implies
cover-hollowness**.  A realization at `λ_ξ` terminal in the class at `ξ` with top-grade supremum
`⊤` is cover-hollow. -/
def StronglyCodedTerminalHollowTarget : Prop :=
  ∀ R : Realization.{u, v} (blockStage ξ) M, R.IsStronglyCodedTerminalAt ξ →
    R.topGradeSup = ⊤ → R.IsCoverHollow


end Targets

/-! ### A point from unbounded growth -/

section Growth

variable {α : Ordinal.{u}} {M : Type v}

/-- **Unbounded growth gives a point of the carrier**: if the top-grade supremum of `R` is `⊤`,
some occurrence has a cell labelled `⊤` of positive grade; its scope is nonempty, so the carrier
is nonempty. -/
theorem nonempty_of_topGradeSup_eq_top {R : Realization.{u, v} α M} (h : R.topGradeSup = ⊤) :
    Nonempty M := by
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, 0 < x.type.topGrade := by
    by_contra! h'
    have hle : R.topGradeSup ≤ 0 := iSup_le fun x ↦ by exact_mod_cast h' x
    simp [h] at hle
  obtain ⟨d, -, hd⟩ : ∃ d, x.type.label d = ⊤ ∧ 0 < x.type.toCellScheme.grade d := by
    by_contra! h'
    exact hx.not_ge (topGrade_le_iff.mpr h')
  obtain ⟨i, -⟩ :=
    card_pos.mp (hd.trans_le (x.type.isWellFormed.isWellFormed.grade_le_card d))
  exact ⟨x.tuple i⟩

end Growth

/-! ### Strongly coded receiving over the empty root -/

section EmptyRoot

variable {α : Ordinal.{u}} {M : Type v} {C : Realization.{u, v} α M}

/-- **Strongly coded receiving over the empty root from positive roots** (native construction):
as the empty-root case of `Realization.hasFiniteCutReceiving_of_pos`, in the strongly coded class.
At a stage that is zero or a limit, let `C` be exactly consistent and covering on a nonempty
carrier, with legal and strongly coded types, receiving every coface with strongly coded rows over
every occurrence of positive arity.  Over an occurrence on no points, a coface `D` with strongly
coded rows (a strongly coded legal stage type on one point) is received: covering gives an
occurrence of positive arity, the strongly coded amalgam over the empty face
(`StageType.HasStronglyCodedCofaceInstances.exists_amalgam_empty`) combines its type with `D` into
a coface with strongly coded rows, which is received over that occurrence and restricted to the
new point by exact consistency. -/
theorem realizesOver_of_arity_eq_zero (hα : Order.IsSuccPrelimit α) (hne : Nonempty M)
    (hl : C.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), C.eval t = some p →
      p.rows.IsStronglyCoded)
    (hc : C.IsConsistent) (hcov : C.IsCovering)
    (hpos : ∀ x : C.Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded →
      ∀ c : Label.{u}, IsPermittedCutoff α c → C.RealizesOver x.tuple (receivingFamily D c))
    (x : C.Occurrence) (hx : x.arity = 0) {D : StageType.{u} α (x.arity + 1)}
    (hD : D ∈ x.type.cofaces) (hDs : D.rows.IsStronglyCoded) {c : Label.{u}}
    (hc' : IsPermittedCutoff α c) : C.RealizesOver x.tuple (receivingFamily D c) := by
  obtain ⟨_ | n, t, p, ht⟩ := x
  · obtain ⟨a⟩ := hne
    obtain ⟨m, u, f, -, hu⟩ :=
      hcov (⟨fun _ ↦ a, fun i j _ ↦ Subsingleton.elim i j⟩ : Fin 1 ↪ M)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨Q, hQ, hQs, hQD⟩ :=
      (HasStronglyCodedCofaceInstances.of_isSuccPrelimit hα).exists_amalgam_empty P D
        ⟨hl u P hP, hsc u P hP⟩ ⟨hD.1, hDs⟩
    obtain ⟨w, -, q, hq, hwq⟩ := hpos ⟨m, u, P, hP⟩ (f 0).pos Q hQ hQs c hc'
    obtain ⟨q', hq', hq'D⟩ := exists_restrictFace_mem_receivingFamily hq hQD
    exact ⟨(Fin.natAddEmb m).trans w, Function.Embedding.ext fun i ↦ i.elim0, q', hq'D,
      (hc w q _ hwq).trans hq'⟩
  · exact absurd hx n.succ_ne_zero

/-- **Strongly coded receiving from positive roots** (native construction): for `C` as in
`Realization.realizesOver_of_arity_eq_zero`, receiving of the cofaces with strongly coded rows over
the occurrences of positive arity gives it over every occurrence. -/
theorem hasFiniteCutReceivingIn_isStronglyCoded_of_pos (hα : Order.IsSuccPrelimit α)
    (hne : Nonempty M) (hl : C.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), C.eval t = some p →
      p.rows.IsStronglyCoded)
    (hc : C.IsConsistent) (hcov : C.IsCovering)
    (hpos : ∀ x : C.Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded →
      ∀ c : Label.{u}, IsPermittedCutoff α c → C.RealizesOver x.tuple (receivingFamily D c)) :
    C.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded := fun x D hD hDs c hc' ↦
  (Nat.eq_zero_or_pos x.arity).elim
    (fun hx ↦ realizesOver_of_arity_eq_zero hα hne hl hsc hc hcov hpos x hx hD hDs hc')
    (fun hx ↦ hpos x hx D hD hDs c hc')

end EmptyRoot

/-! ### The successor -/

section Successor

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Strongly coded receiving of the candidate over positive roots** (native construction): (R4)
for strongly coded cofaces (`Realization.stablyReceivesAt_of_isStronglyCoded`) at the cutoff `γ`,
read as membership in the receiving family (`StageType.mem_receivingFamily_of_capped`). -/
theorem IsStronglyCodedReceiving.realizesOver_stableCandidate_of_pos
    (hR : R.IsStronglyCodedReceiving) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (x : (R.stableCandidate hR.isStablyLawful).Occurrence) (hx : 0 < x.arity)
    {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)} (hD : D ∈ x.type.cofaces)
    (hDs : D.rows.IsStronglyCoded) {c : Label.{u}} (hc : IsPermittedCutoff (blockStage (ξ + 1)) c) :
    (R.stableCandidate hR.isStablyLawful).RealizesOver x.tuple (receivingFamily D c) := by
  induction c using Label.recBotCoeTop with
  | bot => exact absurd hc not_isPermittedCutoff_bot
  | top => exact absurd hc not_isPermittedCutoff_top
  | coe γ =>
    obtain ⟨u, hu, Q, hQ, hS, hl⟩ := stablyReceivesAt_of_isStronglyCoded hR.isConsistent
      hR.isCovering hR.hasLegalTypes hR.isStronglyCoded hR.receiving hnh hgrow hx hD hDs
      (isPermittedCutoff_coe.mp hc)
    exact ⟨u, hu, Q, mem_receivingFamily_of_capped hS hl, hQ⟩

/-- **The successor is in the strongly coded receiving class** (native construction).  Exact
consistency, covering and legal types of the candidate are those of `R`
(`Realization.isConsistent_stableCandidate`, `Realization.isCovering_stableCandidate`,
`Realization.hasLegalTypes_stableCandidate`); its types have the schemes, hence the rows, of the
types of `R`; receiving over positive roots is
`Realization.IsStronglyCodedReceiving.realizesOver_stableCandidate_of_pos`, and over the empty root
`Realization.realizesOver_of_arity_eq_zero`, with the point from unbounded growth
(`Realization.nonempty_of_topGradeSup_eq_top`). -/
theorem isStronglyCodedReceiving_stableCandidate (hR : R.IsStronglyCodedReceiving)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    (R.stableCandidate hR.isStablyLawful).IsStronglyCodedReceiving := by
  have hsc : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (P : StageType.{u} (blockStage (ξ + 1)) n),
      (R.stableCandidate hR.isStablyLawful).eval u = some P → P.rows.IsStronglyCoded := by
    intro _ u P hP
    obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hP
    exact hR.isStronglyCoded u t ht
  have hc := isConsistent_stableCandidate (hlaw := hR.isStablyLawful) hR.isConsistent hR.isCovering
  have hcov := isCovering_stableCandidate (hlaw := hR.isStablyLawful) hR.isCovering
  have hl := hasLegalTypes_stableCandidate (hlaw := hR.isStablyLawful) hR.hasLegalTypes
  exact ⟨hc, hcov, hl, hsc, hasFiniteCutReceivingIn_isStronglyCoded_of_pos
    (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit (nonempty_of_topGradeSup_eq_top hgrow) hl hsc
    hc hcov fun x hx _ hD hDs _ hc' ↦
      hR.realizesOver_stableCandidate_of_pos hnh hgrow x hx hD hDs hc'⟩

/-- **Terminality in the strongly coded receiving class with unbounded growth implies
cover-hollowness** (native construction): otherwise the stable candidate is a successor in the class
(`Realization.isStronglyCodedReceiving_stableCandidate`) reducing to `R`
(`Realization.stableCandidate_reduce`). -/
theorem IsStronglyCodedTerminalAt.isCoverHollow (ht : R.IsStronglyCodedTerminalAt ξ)
    (hgrow : R.topGradeSup = ⊤) : R.IsCoverHollow :=
  not_not.mp fun hnh ↦
    ht.2 ⟨_, isStronglyCodedReceiving_stableCandidate ht.1 hnh hgrow, stableCandidate_reduce⟩

end Successor

/-! ### The targets -/

/-- **Target: the successor in the strongly coded receiving class** (native construction):
`Realization.isStronglyCodedReceiving_stableCandidate` and `Realization.stableCandidate_reduce`. -/
theorem stronglyCodedSuccessorTarget (ξ : Ordinal.{u}) (M : Type v) :
    StronglyCodedSuccessorTarget ξ M :=
  fun _ hR hnh hgrow ↦
    ⟨isStronglyCodedReceiving_stableCandidate hR hnh hgrow, stableCandidate_reduce⟩

/-- **Target: strongly coded receiving of the successor over the empty root** (native
construction): `Realization.realizesOver_of_arity_eq_zero` for the candidate, with the point from
unbounded growth and positive roots from
`Realization.IsStronglyCodedReceiving.realizesOver_stableCandidate_of_pos`. -/
theorem stronglyCodedEmptyRootTarget (ξ : Ordinal.{u}) (M : Type v) :
    StronglyCodedEmptyRootTarget ξ M := fun _ hR hnh hgrow x hx _ hD hDs _ hc ↦
  realizesOver_of_arity_eq_zero (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit
    (nonempty_of_topGradeSup_eq_top hgrow)
    (hasLegalTypes_stableCandidate (hlaw := hR.isStablyLawful) hR.hasLegalTypes)
    (isStronglyCodedReceiving_stableCandidate hR hnh hgrow).isStronglyCoded
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering)
    (fun y hy _ hD' hDs' _ hc' ↦ hR.realizesOver_stableCandidate_of_pos hnh hgrow y hy hD' hDs' hc')
    x hx hD hDs hc

/-- **Target: terminality in the strongly coded receiving class with unbounded growth implies
cover-hollowness** (native construction): `Realization.IsStronglyCodedTerminalAt.isCoverHollow`. -/
theorem stronglyCodedTerminalHollowTarget (ξ : Ordinal.{u}) (M : Type v) :
    StronglyCodedTerminalHollowTarget ξ M :=
  fun _ ht hgrow ↦ ht.isCoverHollow hgrow

end Realization

end VaughtConjecture

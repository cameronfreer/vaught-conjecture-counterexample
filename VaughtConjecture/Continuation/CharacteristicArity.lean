/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GlobalRowAnchor

/-!
# The stable section and the top-grade supremum

Roadmap, Layer 4 (top-grade growth through covers; cover-hollowness and the anchor definition of
hollowness); semantic contract, item 8.  A research file: a native stable-section
characterization of the top-grade supremum (`Realization.topGradeSup`), and the vacuity of the
anchor inequality above the top grade.

**The printed definition.**  [Kni26, Definition 5.4.1, p. 54]: for `α` a countable ordinal that
is zero or a limit and `𝔐` a model of `S^α`, the characteristic arity of `𝔐` is the natural
number `K` such that `α + K` is the supremum of all values `𝔐⁺(Ξ)`, over all `Ξ ∈ dom 𝔐(A)` and
all `A ∈ dom 𝔐`, if there is one, and `∞` otherwise; `𝔐⁺` is the provisional expansion of
[Kni26, Definition 5.3.9, pp. 53–54].

**The native statement.**  At a block stage `λ_ξ`, the values read here are those of the stable
section (`Realization.stableSection`, `VaughtConjecture.Continuation.Candidate`) at every cell of
every occurrence: the label below `λ_ξ` at a cell not labelled `⊤`, the stable label
`λ_ξ + n` or the formal top at a cell labelled `⊤`.  For a model at `λ_ξ`, `λ_ξ + K` is the
least upper bound of these values exactly when the top-grade supremum is `K`
(`Realization.IsModel.isLUB_stableSection_iff`), and no `λ_ξ + K` is their least upper bound
exactly when it is `⊤` (`Realization.IsModel.forall_not_isLUB_stableSection_iff`).  The three
cases are separate statements:

* **top-grade supremum `0`** (`Realization.IsModel.isLUB_stableSection_of_topGradeSup_eq_zero`):
  no cell is labelled `⊤`, every value is a label below `λ_ξ`, and the values are cofinal below
  `λ_ξ` by high-arity dominance (`Realization.IsModel.exists_lt_label`); so the least upper bound
  is `λ_ξ` and is not attained;
* **top-grade supremum `K > 0`** (`Realization.isLUB_stableSection_of_topGradeSup_eq`, with no
  hypothesis on `R`): every stable offset at a cell labelled `⊤` is at most `K`
  (`Realization.stableOffset_le_of_topGradeSup_eq`), since every rooted cover is an occurrence of
  top grade at most `K` and forces no threshold above it
  (`StageType.not_forcesThreshold_of_topGrade_le`); a cell labelled `⊤` of grade `K` has stable
  label at least `λ_ξ + K` by the order law; so the least upper bound `λ_ξ + K` is attained;
* **top-grade supremum `⊤`** (`Realization.not_isLUB_stableSection_of_topGradeSup_eq_top`, with no
  hypothesis on `R`): for every `K` some cell labelled `⊤` has grade above `K`, and its stable
  value exceeds `λ_ξ + K`; so no `λ_ξ + K` is an upper bound.  Nothing is said about the least
  upper bound in this case, nor about whether any stable label is the formal top.

Only the first case uses modelhood, through high-arity dominance and the existence of an
occurrence.

**What this is not.**  This is a characterization of `Realization.topGradeSup` by the stable
section, not a completion of the manuscript correspondence of [Kni26, Definition 5.4.1].  The
stable section plays the role of `𝔐⁺`, but the provisional values `p⁺` of
[Kni26, Definition 5.3.1, p. 49] and the eventual values of [Kni26, Definition 5.3.9] are not
compared with the provisional and stable offsets here: the correspondence of `𝔐⁺` with the
stable section is open, and so is the correspondence between the models of `S^α` of
[Kni26, Definition 3.2.1] and the models of this repository.  The printed definition also allows
`α = 0`, which is not a block stage; that case is outside these statements.

**The anchor inequality above the top grade.**  If every cell labelled `⊤` has grade at most `K`
(`R.topGradeSup ≤ K`), then at the anchor bound `K' = K + 1` no cell labelled `⊤` has grade at
least `K'`, so the inequality "minimal at infinity" of the native global-cell rendering of
[Kni26, Definition 5.4.2, p. 56] has no instance to test and holds at every cell
(`Realization.isMinimalAtInfinity_add_one_of_topGradeSup_le`); every cell labelled `⊤` is then a
global row anchor and a row anchor at `K + 1`
(`Realization.isGlobalRowAnchor_add_one_of_topGradeSup_le`,
`Realization.isRowAnchor_add_one_of_topGradeSup_le`).  The bound `K` here bounds grades of cells
labelled `⊤`; the anchor bound `K'` is the existentially quantified bound of the inequality.
With top-grade supremum `K > 0` there is a cell labelled `⊤`, so a global row anchor exists
(`Realization.hasGlobalRowAnchor_of_topGradeSup_eq`), and at a block stage the realization is not
cover-hollow (`Realization.not_isCoverHollow_of_topGradeSup_eq`, from the bound on stable offsets
and `Realization.isCoverHollow_iff_forall_stableLabel_eq_top`).  None of these uses modelhood.
With top-grade supremum `0` there is no cell labelled `⊤` and nothing is claimed.

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

Characteristic arity is [Kni26, Definition 5.4.1, p. 54]; the provisional expansion is
[Kni26, Definitions 5.3.1 and 5.3.9, pp. 49 and 53–54]; high-arity dominance is clause 4(c) of
[Kni26, Definition 3.2.1, p. 31]; the anchor at infinity is [Kni26, Definition 5.4.2, p. 56].
-/

universe u v

namespace VaughtConjecture

open Order Label

namespace Realization

/-! ### Cofinality of labels -/

/-- **Labels are cofinal below the stage** in a model: for every `γ` below the stage, some cell of
some occurrence has a label above `γ` (high-arity dominance over any occurrence). -/
theorem IsModel.exists_lt_label {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}
    (hR : R.IsModel) {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (x : R.Occurrence) (a : Fin x.type.card), (γ : Label.{u}) < x.type.label a := by
  obtain ⟨x⟩ := hR.nonempty_occurrence
  obtain ⟨u, -, q, ⟨d, -, hd⟩, hq⟩ := hR.dominance x γ hγ
  exact ⟨⟨_, u, q, hq⟩, d, hd⟩

/-! ### The anchor inequality above the top grade -/

section Vacuity

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M} {K : ℕ}

/-- If the top-grade supremum is at most `K`, every cell labelled `⊤` of every occurrence has grade
at most `K`. -/
theorem grade_le_of_topGradeSup_le (hK : R.topGradeSup ≤ K) (z : R.Occurrence)
    {θ : Fin z.type.card} (hθ : z.type.label θ = ⊤) : z.type.toCellScheme.grade θ ≤ K :=
  (StageType.grade_le_topGrade hθ).trans (by exact_mod_cast z.topGrade_le_topGradeSup.trans hK)

/-- **The anchor inequality is vacuous above the top grade**: if every cell labelled `⊤` has grade
at most `K`, then at the bound `K + 1` no cell labelled `⊤` has grade at least the bound, and
every cell of every occurrence is minimal at infinity. -/
theorem isMinimalAtInfinity_add_one_of_topGradeSup_le (hK : R.topGradeSup ≤ K)
    (x : R.Occurrence) (a : Fin x.type.card) : R.IsMinimalAtInfinity x a (K + 1) :=
  fun z _ _ θ hθ hKθ ↦ absurd (grade_le_of_topGradeSup_le hK z hθ) (by omega)

/-- **Every cell labelled `⊤` is a global row anchor above the top grade**: if every cell labelled
`⊤` has grade at most `K`, a cell labelled `⊤` is a global row anchor at the bound `K + 1`. -/
theorem isGlobalRowAnchor_add_one_of_topGradeSup_le (hK : R.topGradeSup ≤ K)
    {x : R.Occurrence} {a : Fin x.type.card} (ha : x.type.label a = ⊤) :
    R.IsGlobalRowAnchor x a (K + 1) :=
  ⟨ha, isMinimalAtInfinity_add_one_of_topGradeSup_le hK x a⟩

/-- **Every cell labelled `⊤` is a row anchor above the top grade**: the rooted form of
`Realization.isGlobalRowAnchor_add_one_of_topGradeSup_le`
(`Realization.IsGlobalRowAnchor.isRowAnchor`). -/
theorem isRowAnchor_add_one_of_topGradeSup_le (hK : R.topGradeSup ≤ K) {x : R.Occurrence}
    {a : Fin x.type.card} (ha : x.type.label a = ⊤) : R.IsRowAnchor x a (K + 1) :=
  (isGlobalRowAnchor_add_one_of_topGradeSup_le hK ha).isRowAnchor

/-- A positive top-grade supremum has a cell labelled `⊤`. -/
theorem exists_label_eq_top_of_topGradeSup_ne_zero (h : R.topGradeSup ≠ 0) :
    ∃ (x : R.Occurrence) (a : Fin x.type.card), x.type.label a = ⊤ := by
  by_contra! hne
  exact h (topGradeSup_eq_zero_iff.mpr fun x a ↦ hne x a)

/-- **A positive finite top-grade supremum gives a global row anchor**, at the bound `K + 1`, with
no hypothesis on `R`. -/
theorem hasGlobalRowAnchor_of_topGradeSup_eq (hK : R.topGradeSup = K) (h0 : 0 < K) :
    R.HasGlobalRowAnchor := by
  obtain ⟨x, a, ha⟩ := exists_label_eq_top_of_topGradeSup_ne_zero
    (by rw [hK]; exact_mod_cast h0.ne')
  exact ⟨x, a, K + 1, isGlobalRowAnchor_add_one_of_topGradeSup_le hK.le ha⟩

end Vacuity

/-! ### The stable offset under bounded growth -/

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- `λ_ξ + K` lies below the next block stage. -/
theorem coe_add_lt_blockStage_add_one (K : ℕ) : blockStage ξ + K < blockStage (ξ + 1) := by
  rw [blockStage_add_one]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 K) _

/-- **Bounded growth bounds the stable offset**: if the top-grade supremum is `K`, the stable
offset at a cell labelled `⊤` is at most `K`.  Every rooted cover is an occurrence, so its cells
labelled `⊤` have grade at most `K`, and it forces no threshold above `K`
(`StageType.not_forcesThreshold_of_topGrade_le`).  No hypothesis on `R`. -/
theorem stableOffset_le_of_topGradeSup_eq {K : ℕ} (hK : R.topGradeSup = K) {k : ℕ}
    (u : Fin k ↪ M) {t : StageType.{u} (blockStage ξ) k} (d : Fin t.card)
    (hd : t.label d = ⊤) :
    R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤ K := by
  refine iSup₂_le fun x hx ↦ ?_
  obtain ⟨s, -, hs⟩ := hx
  have hq : ∀ c, x.2.1.label c = ⊤ → x.2.1.toCellScheme.grade c ≤ K := fun c hc ↦
    grade_le_of_topGradeSup_le hK.le ⟨x.1, ⟨s, hs.injective⟩, x.2.1, hs.eval_eq⟩ hc
  refine iSup₂_le fun n hn ↦ ?_
  by_contra hlt
  have hKn : K + 1 ≤ n := by
    have : (K : ℕ∞) < n := lt_of_not_ge hlt
    exact_mod_cast this
  exact StageType.not_forcesThreshold_of_topGrade_le (coe_add_lt_blockStage_add_one K) hq
    hn.restrictFace_eq hd (hn.mono hKn)

/-- **Bounded growth bounds the stable section**: if the top-grade supremum is `K`, every value of
the stable section is at most `λ_ξ + K`.  No hypothesis on `R`. -/
theorem stableSection_le_of_topGradeSup_eq {K : ℕ} (hK : R.topGradeSup = K) {k : ℕ}
    (u : Fin k ↪ M) (t : StageType.{u} (blockStage ξ) k) (d : Fin t.card) :
    R.stableSection u t d ≤ ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) := by
  by_cases hd : t.label d = ⊤
  · rw [stableSection_of_eq_top hd, stableLabel, ← ofOffset_natCast]
    exact ofOffset_mono (stableOffset_le_of_topGradeSup_eq hK u d hd)
  · rw [stableSection_of_ne_top hd]
    exact ((t.atStage d).resolve_right hd).le.trans (Label.coe_le_coe_add _ K)

/-- **The order law on the stable section**: at a cell labelled `⊤` of an occurrence, the stable
section is at least `λ_ξ` plus the grade of the cell. -/
theorem coe_add_grade_le_stableSection (x : R.Occurrence) {d : Fin x.type.card}
    (hd : x.type.label d = ⊤) :
    ((blockStage ξ + x.type.toCellScheme.grade d : Ordinal.{u}) : Label.{u}) ≤
      R.stableSection x.tuple x.type d := by
  rcases stableSection_eq_top_or_exists x.eval_tuple hd with h | ⟨i, hi, h⟩ <;> rw [h]
  · exact le_top
  · exact_mod_cast add_le_add_right (Nat.cast_le.mpr hi) _

/-- **Bounded growth makes every cell labelled `⊤` an anchor at the top**: at a block stage, if
the top-grade supremum is `K > 0`, the realization is not cover-hollow.  A cell labelled `⊤`
exists, and its stable offset is at most `K`, so its stable label is not the formal top
(`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`).  No hypothesis on `R`. -/
theorem not_isCoverHollow_of_topGradeSup_eq {K : ℕ} (hK : R.topGradeSup = K) (h0 : 0 < K) :
    ¬ R.IsCoverHollow := by
  obtain ⟨x, a, ha⟩ := exists_label_eq_top_of_topGradeSup_ne_zero
    (by rw [hK]; exact_mod_cast h0.ne')
  intro hh
  have htop := (isCoverHollow_iff_forall_stableLabel_eq_top.mp hh) x a ha
  rw [stableLabel, ofOffset_eq_top_iff] at htop
  have hle := stableOffset_le_of_topGradeSup_eq hK x.tuple a ha
  rw [htop] at hle
  exact ENat.natCast_ne_top K (top_le_iff.mp hle)

/-! ### The three cases -/

/-- **Top-grade supremum `0`**: in a model at a block stage with top-grade supremum `0`, the least
upper bound of the values of the stable section is `λ_ξ`.  No cell is labelled `⊤`, so every value
is a label below `λ_ξ`, and these labels are cofinal below `λ_ξ`
(`Realization.IsModel.exists_lt_label`). -/
theorem IsModel.isLUB_stableSection_of_topGradeSup_eq_zero (hR : R.IsModel)
    (h0 : R.topGradeSup = 0) :
    IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
        R.stableSection x.tuple x.type a = ℓ} ((blockStage ξ : Ordinal.{u}) : Label.{u}) := by
  have htf := topGradeSup_eq_zero_iff.mp h0
  refine ⟨?_, fun b hb ↦ ?_⟩
  · rintro _ ⟨x, a, rfl⟩
    rw [stableSection_of_ne_top (htf x a)]
    exact ((x.type.atStage a).resolve_right (htf x a)).le
  · by_contra! hlt
    obtain ⟨γ, hγ, hbγ⟩ : ∃ γ : Ordinal.{u}, γ < blockStage ξ ∧ b ≤ (γ : Label.{u}) := by
      induction b using Label.recBotCoeTop with
      | bot => exact ⟨0, (isSuccLimit_blockStage ξ).bot_lt, bot_le⟩
      | coe o => exact ⟨o, WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt), le_rfl⟩
      | top => exact absurd hlt (not_lt.mpr le_top)
    obtain ⟨x, a, hxa⟩ := hR.exists_lt_label hγ
    have hmem := hb ⟨x, a, rfl⟩
    rw [stableSection_of_ne_top (htf x a)] at hmem
    exact (hxa.trans_le (hmem.trans hbγ)).false

/-- **Top-grade supremum `K > 0`**: at a block stage, if the top-grade supremum is `K > 0`, then
`λ_ξ + K` is the least upper bound of the values of the stable section, and it is attained at a
cell labelled `⊤` of grade `K`.  No hypothesis on `R`. -/
theorem isLUB_stableSection_of_topGradeSup_eq {K : ℕ} (hK : R.topGradeSup = K) (h0 : 0 < K) :
    IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
        R.stableSection x.tuple x.type a = ℓ}
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) := by
  classical
  have hne : Nonempty R.Occurrence := by
    obtain ⟨x, -⟩ := exists_label_eq_top_of_topGradeSup_ne_zero
      (by rw [hK]; exact_mod_cast h0.ne')
    exact ⟨x⟩
  obtain ⟨x, hx⟩ := ENat.exists_eq_iSup_of_lt_top
    (f := fun y : R.Occurrence ↦ (y.type.topGrade : ℕ∞))
    (show R.topGradeSup < ⊤ from hK ▸ ENat.natCast_lt_top K)
  have hxK : x.type.topGrade = K := by exact_mod_cast hx.trans hK
  obtain ⟨d, hd, hdK⟩ : ∃ d, x.type.label d = ⊤ ∧ x.type.toCellScheme.grade d = K := by
    have hpos : 0 < x.type.topGrade := hxK ▸ h0
    unfold StageType.topGrade at hpos hxK
    set s := ({d | x.type.label d = ⊤} : Finset (Fin x.type.card)) with hs
    rcases s.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sup_empty] at hpos
      exact absurd hpos (lt_irrefl 0)
    · obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_eq_sup s hne x.type.toCellScheme.grade
      exact ⟨d, by simpa [hs] using hd, hd'.symm.trans hxK⟩
  refine IsGreatest.isLUB ⟨⟨x, d, le_antisymm (stableSection_le_of_topGradeSup_eq hK _ _ _) ?_⟩,
    ?_⟩
  · simpa [hdK] using coe_add_grade_le_stableSection x hd
  · rintro _ ⟨y, a, rfl⟩
    exact stableSection_le_of_topGradeSup_eq hK _ _ _

/-- **Top-grade supremum `⊤`**: at a block stage, if the top-grade supremum is `⊤`, then for every
`K` some value of the stable section exceeds `λ_ξ + K` (at a cell labelled `⊤` of grade above
`K`, by the order law), so `λ_ξ + K` is not an upper bound, let alone the least one.  Nothing is
said about the least upper bound of the values, nor about whether any value is the formal top.
No hypothesis on `R`. -/
theorem not_isLUB_stableSection_of_topGradeSup_eq_top (hgrow : R.topGradeSup = ⊤) (K : ℕ) :
    ¬ IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
        R.stableSection x.tuple x.type a = ℓ}
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, K < x.type.topGrade := by
    by_contra! h
    have hle : R.topGradeSup ≤ K := iSup_le fun x ↦ Nat.cast_le.mpr (h x)
    simp [hgrow] at hle
  obtain ⟨d, hd, hKd⟩ : ∃ d, x.type.label d = ⊤ ∧ K < x.type.toCellScheme.grade d := by
    by_contra! h
    exact hx.not_ge (StageType.topGrade_le_iff.mpr h)
  intro hlub
  have hle := hlub.1 ⟨x, d, rfl⟩
  have hlt : ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) <
      ((blockStage ξ + x.type.toCellScheme.grade d : Ordinal.{u}) : Label.{u}) := by
    exact_mod_cast add_lt_add_right (Nat.cast_lt.mpr hKd) _
  exact (hlt.trans_le (coe_add_grade_le_stableSection x hd)).not_ge hle

/-! ### The characterization -/

/-- `λ_ξ + K` determines `K`. -/
theorem coe_add_natCast_injective {K K' : ℕ}
    (h : ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) =
      ((blockStage ξ + K' : Ordinal.{u}) : Label.{u})) : K = K' := by
  have h' : blockStage ξ + (K : Ordinal.{u}) = blockStage ξ + K' :=
    WithTop.coe_injective (WithBot.coe_injective h)
  exact_mod_cast add_left_cancel h'

/-- **A native stable-section characterization of the top-grade supremum**: in a model at a
block stage, `λ_ξ + K` is the least upper bound of the values of the stable section over all
cells of all occurrences exactly when the top-grade supremum is `K`.  This reads the wording of
[Kni26, Definition 5.4.1, p. 54] with the stable section in the role of `𝔐⁺`; the correspondence
of `𝔐⁺` with the stable section, and of the models of [Kni26, Definition 3.2.1] with those here,
is open, so this is not a completion of the manuscript correspondence of that definition.  The
three cases are `Realization.IsModel.isLUB_stableSection_of_topGradeSup_eq_zero`,
`Realization.isLUB_stableSection_of_topGradeSup_eq` and
`Realization.not_isLUB_stableSection_of_topGradeSup_eq_top`. -/
theorem IsModel.isLUB_stableSection_iff (hR : R.IsModel) (K : ℕ) :
    IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
        R.stableSection x.tuple x.type a = ℓ}
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) ↔ R.topGradeSup = K := by
  have hzero : IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
      R.stableSection x.tuple x.type a = ℓ} ((blockStage ξ + (0 : ℕ) : Ordinal.{u}) : Label.{u})
      ↔ R.topGradeSup = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simpa using hR.isLUB_stableSection_of_topGradeSup_eq_zero h⟩
    induction hs : R.topGradeSup using ENat.recTopCoe with
    | top => exact absurd h (not_isLUB_stableSection_of_topGradeSup_eq_top hs 0)
    | coe K' =>
      rcases Nat.eq_zero_or_pos K' with rfl | hK'
      · rfl
      · exact absurd (coe_add_natCast_injective
          (h.unique (isLUB_stableSection_of_topGradeSup_eq hs hK'))) hK'.ne
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using hzero
  refine ⟨fun h ↦ ?_, fun h ↦ isLUB_stableSection_of_topGradeSup_eq h hK⟩
  induction hs : R.topGradeSup using ENat.recTopCoe with
  | top => exact absurd h (not_isLUB_stableSection_of_topGradeSup_eq_top hs K)
  | coe K' =>
    rcases Nat.eq_zero_or_pos K' with rfl | hK'
    · have h0 := (hR.isLUB_stableSection_of_topGradeSup_eq_zero (by exact_mod_cast hs))
      have := coe_add_natCast_injective (K := K) (K' := 0) (h.unique (by simpa using h0))
      omega
    · rw [coe_add_natCast_injective (h.unique (isLUB_stableSection_of_topGradeSup_eq hs hK'))]

/-- **Unbounded growth, in the same terms**: in a model at a block stage, no `λ_ξ + K` is the
least upper bound of the values of the stable section exactly when the top-grade supremum is
`⊤`.  The statement concerns the values `λ_ξ + K` only: it does not say that the least upper
bound is the formal top, nor that any cell has the formal top as its stable label. -/
theorem IsModel.forall_not_isLUB_stableSection_iff (hR : R.IsModel) :
    (∀ K : ℕ, ¬ IsLUB {ℓ : Label.{u} | ∃ (x : R.Occurrence) (a : Fin x.type.card),
        R.stableSection x.tuple x.type a = ℓ}
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u})) ↔ R.topGradeSup = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ not_isLUB_stableSection_of_topGradeSup_eq_top h⟩
  by_contra hne
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hne
  exact h K ((hR.isLUB_stableSection_iff K).mpr hK.symm)

end Realization

end VaughtConjecture

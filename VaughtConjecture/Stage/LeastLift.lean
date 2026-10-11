/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.MarkedCap

/-!
# The least lift of a stage type, and forcing read by the rows

Roadmap, Layer 3, 3.1 ("The attained least lift", and its derived statement (b), the threshold
characterization, in its per-cover form); Layer 1 (stage types and stage reduction).  Everything
here concerns stage types only: no realization and no model is involved.

Throughout, `β` is zero or a limit and `α` a second stage; in the application `β = λ_ξ` and
`α = λ_{ξ+1}` are consecutive block stages.

**Lifts on the fixed scheme.**  A *lift labelling* of a stage type `q` at `β` to `α`
(`StageType.IsLiftLabelling`) is a labelling of the cells of `q`, lawful for the rows of `q`,
whose labels occur at `α` and whose stage reduction to `β` is the labelling of `q`.  The lift
labellings are exactly the labellings of the stage types at `α` reducing to `q`
(`StageType.isLiftLabelling_iff`): stage reduction keeps the scheme, so a lift never changes the
scheme or the rows, only the labels.  At a cell whose label in `q` is below `β`, every lift
labelling has that label (`StageType.IsLiftLabelling.eq_label_of_ne_top`).

**The fibre gap** (`StageType.IsMarker.label_eq_bandMap_or_le`, compiled in this repository
(theorem named)).  Let `c` be a top cap of `q` of grade `N` and `r` a marker of `c`, with the row of
`c` reading `r` at `μ + j` (`μ` zero or a limit).  For every stage type `Q` at `α` reducing to `q`
and every cell `e` labelled `⊤` in `q`, either `Q` has at `e` the label
`bandMap β μ N (q.rowAt c e)` of the band lift (`StageType.IsMarker.exists_lift`), or `Q` is at
least `β + N` at `e`.  Hence the band label is at most the label of every lift
(`StageType.IsMarker.bandMap_rowAt_le_label`).  These two lower-bound statements have weaker
premises than the attained least lift below: `β` zero or a limit, with no legality of `q`, no bound
on `α`, and no coding beyond the range normalization carried by every stage type (they do not
assert that the band labelling is itself a lift).  The proof reads locality of
`Q` at `c`, with a witness `(g, σ)`: the label `β + i` of `Q` at `e` (`i < N`) lies strictly below
the label of `Q` at `c`, which is at least `β + N` by the order law, so the shifter sends the row
entry `a` at `e` to `β + i`; at the marker the shifter is at least `β` and at most `β + i`, so
commuting it with visibility replacement at `N` (clause 5, as `β + i` is below `g N`) excludes
`visibilityReplace N N (μ + j) ≤ a`; this places `a` at `μ + j'` with `j' < N`, and commuting the
shifter with visibility replacement at `(N, j')` gives `i = j'`.

**The attained least lift** (`StageType.IsMarker.isLeast_bandLabelling`,
`StageType.exists_isLeast_isLiftLabelling`, compiled in this repository (theorem named)).  For a
legal `q` at a limit `β` and `β + ω ≤ α`, one lift labelling is least among all lift labellings,
pointwise at every cell simultaneously: the labelling of `q` when `q` is top-free, and otherwise
the band labelling of a top cap and a marker, `bandMap β μ N (q.rowAt c ·)` at the cells labelled
`⊤` and the label of `q` elsewhere.  The premises of the attained leastness are exactly these:
`q` legal, `β` a limit, and `β + ω ≤ α`.  The proof uses them to show that the least element is a
lift labelling at all (the band lift, `StageType.IsMarker.exists_lift`, assumes all three) and that
a top cap exists (from legality); only the lower bound, the fibre gap above, is proved without
them.

**The threshold characterization** (compiled in this repository (theorem named)).  For a legal
rooted cover `(q, f)` of a root `p` at a limit `β`, `β + ω ≤ α`, a cell `d` of `p` labelled `⊤`
transported to the cell `e` of `q`, a top cap `c` of grade `N`, and a marker `r` of `c` read at
`μ + j`, the following are equivalent, for every `n : ℕ`:

* `(q, f)` forces the threshold `n` at `d` (`StageType.ForcesThreshold`);
* every lift of `q` is at least `β + n` at `e` (`StageType.forcesThreshold_iff_forall_lift`);
* any least lift labelling `ℓ₀` of `q` is at least `β + n` at `e`
  (`StageType.forcesThreshold_iff_coe_add_le_of_isLeast`; this equivalence uses only that `β` is
  zero or a limit, with `q` restricting to `p` and `e` transported from `d`);
* the band label is at least `β + n` (`StageType.IsMarker.forcesThreshold_iff_coe_add_le_bandMap`);
* `n ≤ N` and `visibilityReplace N n (q.rowAt c r) ≤ q.rowAt c e`
  (`StageType.IsMarker.forcesThreshold_iff_le_grade_and_visibilityReplace_rowAt_le`, the converse
  of `StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`).

So the provisional offset is the offset of the band label
(`StageType.IsMarker.ofOffset_provisionalOffset`): `Label.ofOffset β` of the provisional offset is
`bandMap β μ N (q.rowAt c e)`, and the provisional offset is finite and at most `N`
(`StageType.IsMarker.provisionalOffset_le_grade`).  The thresholds of all cells of a cover are read
off one lawful labelling, the least lift, not off witnesses chosen separately at the cells.

**Coding.**  Strong coding of the rows (`CellScheme.Rows.IsStronglyCoded`) is not assumed anywhere
here: the statements hold for every legal stage type, strongly coded or not.  The only coding used
is the range normalization of stage types (`Scheme.IsCoded`), through the band lift, which needs
the entry of the row of the top cap at the marker to be an ordinal.

**Open, not claimed here.**  Nothing here concerns realizations.  The supremum forms over the
rooted covers of a realization (through `Realization.stableOffset`) of the threshold
characterization and of the limit-stage monotonicity, stated with the least lift, are not proved
here and remain open, as do any statements about cover-hollowness and modelhood drawn from them; no
change to the normalization of `Continuation/Normalization` is made.

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.

## References

Locality and the transformation relation are [Kni26, Definition 2.3.9]; the band map is the
post-composition in the proof of [Kni26, Lemma 5.3.5]; stage reduction is
[Kni26, Definition 3.1.2].
-/

universe u

namespace VaughtConjecture

open Finset Order Label
open scoped Ordinal

namespace Label

variable {o : Ordinal.{u}} {x : Label.{u}}

/-- A label at least `o` and below `o + ω` is `o + i` for a natural number `i`. -/
theorem exists_eq_coe_add_natCast_of_le_of_lt (h₀ : (o : Label.{u}) ≤ x)
    (h : x < ((o + ω : Ordinal.{u}) : Label.{u})) :
    ∃ i : ℕ, x = ((o + i : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd h₀ (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd h (not_lt.mpr le_top)
  | coe ν =>
    obtain ⟨i, rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
      (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h₀))
      (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))
    exact ⟨i, rfl⟩

/-- `o + i ≤ o + n` as labels exactly when `i ≤ n`. -/
theorem coe_add_natCast_le_coe_add_natCast_iff {i n : ℕ} :
    ((o + i : Ordinal.{u}) : Label.{u}) ≤ ((o + n : Ordinal.{u}) : Label.{u}) ↔ i ≤ n := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, add_le_add_iff_left, Nat.cast_le]

/-- `o + n < o + ω` as labels. -/
theorem coe_add_natCast_lt_coe_add_omega0 (n : ℕ) :
    ((o + n : Ordinal.{u}) : Label.{u}) < ((o + ω : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left o).mpr (Ordinal.natCast_lt_omega0 n)))

/-- A label at least `o` and below `o + N` is `o + i` for some `i < N`. -/
theorem exists_lt_eq_coe_add_natCast_of_le_of_lt {N : ℕ} (h₀ : (o : Label.{u}) ≤ x)
    (h : x < ((o + N : Ordinal.{u}) : Label.{u})) :
    ∃ i : ℕ, i < N ∧ x = ((o + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨i, rfl⟩ := exists_eq_coe_add_natCast_of_le_of_lt h₀
    (h.trans (coe_add_natCast_lt_coe_add_omega0 N))
  exact ⟨i, lt_of_not_ge fun hNi ↦ h.not_ge (coe_add_natCast_le_coe_add_natCast_iff.mpr hNi), rfl⟩

/-- **The band map reads a visibility replacement.**  Let `μ` be zero or a limit, `n ≤ N`, and
`x` a label at least `μ + j`.  If `visibilityReplace N n (μ + j) ≤ x`, the band map from `μ` to
`β` at `N` is at least `β + n` at `x`. -/
theorem coe_add_le_bandMap_of_visibilityReplace_le {β μ : Ordinal.{u}} (hμ : IsSuccPrelimit μ)
    {N n j : ℕ} (hn : n ≤ N) (hjx : ((μ + j : Ordinal.{u}) : Label.{u}) ≤ x)
    (h : visibilityReplace N n ((μ + j : Ordinal.{u}) : Label.{u}) ≤ x) :
    ((β + n : Ordinal.{u}) : Label.{u}) ≤ bandMap β μ N x := by
  by_cases hω : ((μ + ω : Ordinal.{u}) : Label.{u}) ≤ x
  · rw [bandMap_of_le ((coe_add_natCast_lt_coe_add_omega0 N).le.trans hω)]
    exact coe_add_natCast_le_coe_add_natCast_iff.mpr hn
  obtain ⟨j', rfl⟩ := exists_eq_coe_add_natCast_of_le_of_lt ((coe_le_coe_add μ j).trans hjx)
    (not_le.mp hω)
  have hjj' : j ≤ j' := coe_add_natCast_le_coe_add_natCast_iff.mp hjx
  rw [bandMap_coe_add_natCast, coe_add_natCast_le_coe_add_natCast_iff]
  refine le_min ?_ hn
  rw [visibilityReplace_coe_add hμ] at h
  split_ifs at h with hjN
  · exact coe_add_natCast_le_coe_add_natCast_iff.mp h
  · exact hn.trans ((not_lt.mp hjN).trans hjj')

end Label

namespace StageType

variable {α β : Ordinal.{u}} {m k : ℕ} {q : StageType.{u} β m} {c r e : Fin q.card}

/-! ### Lift labellings on the fixed scheme -/

/-- A **lift labelling** of `q` to `α`: a labelling of the cells of `q`, lawful for the rows of
`q`, whose labels occur at `α` and reduce at `β` to the labels of `q`. -/
def IsLiftLabelling (α : Ordinal.{u}) (q : StageType.{u} β m) (ℓ : Fin q.card → Label.{u}) :
    Prop :=
  q.rows.IsLawful ℓ ∧ (∀ d, AtStage α (ℓ d)) ∧ ∀ d, Label.reduce β (ℓ d) = q.label d

/-- A stage type reducing to `q` has the cells of `q`. -/
theorem card_eq_of_reduce_eq {hβ : IsSuccPrelimit β} {Q : StageType.{u} α m}
    (hQ : Q.reduce hβ = q) : q.card = Q.card :=
  congrArg (fun t : StageType.{u} β m ↦ t.card) hQ.symm

/-- **Lift labellings are the labellings of the lifts**: a labelling of the cells of `q` is a lift
labelling to `α` exactly when it is, position by position, the labelling of a stage type at `α`
reducing to `q`. -/
theorem isLiftLabelling_iff (hβ : IsSuccPrelimit β) {ℓ : Fin q.card → Label.{u}} :
    q.IsLiftLabelling α ℓ ↔ ∃ Q : StageType.{u} α m, Q.reduce hβ = q ∧
      ∀ (d : Fin q.card) (d' : Fin Q.card), (d' : ℕ) = d → Q.label d' = ℓ d := by
  refine ⟨fun ⟨hlaw, hat, hred⟩ ↦ ?_, fun ⟨Q, hQ, hℓ⟩ ↦ ?_⟩
  · refine ⟨⟨q.toScheme, ℓ, q.isWellFormed, q.isCoded, hlaw, hat⟩,
      ext rfl fun i i' hii' ↦ ?_, fun d d' hdd' ↦ congrArg ℓ (Fin.ext hdd')⟩
    obtain rfl : i = i' := Fin.ext hii'
    exact hred i
  · subst hQ
    obtain rfl : ℓ = Q.label := funext fun d ↦ (hℓ d d rfl).symm
    exact ⟨Q.isLawful, Q.atStage, fun _ ↦ rfl⟩

/-- At a cell whose label in `q` is not the formal top, a lift labelling has the label of `q`. -/
theorem IsLiftLabelling.eq_label_of_ne_top {ℓ : Fin q.card → Label.{u}}
    (h : q.IsLiftLabelling α ℓ) {d : Fin q.card} (hd : q.label d ≠ ⊤) : ℓ d = q.label d := by
  have hlt : ℓ d < β := not_le.mp fun h' ↦ hd ((h.2.2 d).symm.trans (Label.reduce_of_le h'))
  rw [← h.2.2 d, Label.reduce_of_lt hlt]

/-- At a cell labelled `⊤` in `q`, a lift labelling is at least `β`. -/
theorem IsLiftLabelling.coe_le_of_eq_top {ℓ : Fin q.card → Label.{u}}
    (h : q.IsLiftLabelling α ℓ) {d : Fin q.card} (hd : q.label d = ⊤) : (β : Label.{u}) ≤ ℓ d :=
  Label.reduce_eq_top_iff.mp ((h.2.2 d).trans hd)

/-! ### The fibre gap at a marker -/

/-- **The fibre gap at a marker.**  Let `β` be zero or a limit, `c` a top cap of `q` of grade `N`,
and `r` a marker of `c` whose row entry is `μ + j` (`μ` zero or a limit).  Every stage type `Q` at
`α` reducing to `q` has, at a cell `e` labelled `⊤` in `q`, either the band label
`bandMap β μ N (q.rowAt c e)` or a label at least `β + N`.  Premises: `β` zero or a limit; no
legality of `q` and no bound on `α`.  This is a lower bound only: that the band labelling is a lift
is `StageType.IsMarker.isLeast_bandLabelling`, under stronger premises. -/
theorem IsMarker.label_eq_bandMap_or_le (hβ : IsSuccPrelimit β) {Q : StageType.{u} α m}
    (hQ : Q.reduce hβ = q) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {μ : Ordinal.{u}} {j : ℕ}
    (hμ : IsSuccPrelimit μ) (hrj : q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}))
    (he : q.label e = ⊤) (e' : Fin Q.card) (he' : (e' : ℕ) = e) :
    Q.label e' = bandMap β μ (q.toCellScheme.grade c) (q.rowAt c e) ∨
      ((β + q.toCellScheme.grade c : Ordinal.{u}) : Label.{u}) ≤ Q.label e' := by
  subst hQ
  obtain rfl : e' = e := Fin.ext he'
  -- the lift is at least `β` at the cells labelled `⊤`, and at least `β + N` at the top cap
  have hβle {x : Fin Q.card} (hx : (Q.reduce hβ).label x = ⊤) : (β : Label.{u}) ≤ Q.label x :=
    Label.reduce_eq_top_iff.mp hx
  set N := Q.toCellScheme.grade c with hN
  change Q.label e' = bandMap β μ N ((Q.reduce hβ).rowAt c e') ∨
    ((β + N : Ordinal.{u}) : Label.{u}) ≤ Q.label e'
  have hcN : ((β + N : Ordinal.{u}) : Label.{u}) ≤ Q.label c :=
    coe_add_le_of_isSelfVisible hβ (hβle hc.2.1) (Q.isLawful.orderly c)
  by_cases hbig : ((β + N : Ordinal.{u}) : Label.{u}) ≤ Q.label e'
  · exact .inr hbig
  left
  obtain ⟨i, hiN, hei⟩ := exists_lt_eq_coe_add_natCast_of_le_of_lt (hβle he) (not_le.mp hbig)
  have hiβN : ((β + i : Ordinal.{u}) : Label.{u}) < ((β + N : Ordinal.{u}) : Label.{u}) :=
    lt_of_not_ge fun h ↦ hiN.not_ge (coe_add_natCast_le_coe_add_natCast_iff.mp h)
  -- locality of the lift at the top cap
  obtain ⟨g, σ, hw, heq⟩ := Q.isLawful.locality c
  have hcc := Q.toCellScheme.mem_below_gradedIndex c
  have hgN : Q.label c ≤ g N := by
    have h := heq ⟨c, hcc⟩
    change min (Q.label c) (Q.label c) = min (σ (Q.rows.row c ⟨c, hcc⟩)) (g N) at h
    rw [min_self] at h
    exact h.trans_le (min_le_right _ _)
  have hig : ((β + i : Ordinal.{u}) : Label.{u}) < g N := (hiβN.trans_le hcN).trans_le hgN
  -- the cell `e` and the marker lie below the top cap
  have hec := hc.mem_below he
  have hrc := hr.2.1
  set a := Q.rows.row c ⟨e', hec⟩ with ha
  set v := Q.rows.row c ⟨r, hrc⟩ with hv
  have hrowe : (Q.reduce hβ).rowAt c e' = a := Scheme.rowAt_of_mem hec
  have hrowr : (Q.reduce hβ).rowAt c r = v := Scheme.rowAt_of_mem hrc
  -- the shifter reads the row entry at `e` as the label `β + i`
  have hσa : σ a = ((β + i : Ordinal.{u}) : Label.{u}) := by
    have h := heq ⟨e', hec⟩
    change min (Q.label e') (Q.label c) = min (σ a) (g (Q.toCellScheme.grade e')) at h
    rw [hei, min_eq_left (hiβN.trans_le hcN).le] at h
    have hge : g N ≤ g (Q.toCellScheme.grade e') := hw.antitone (hc.2.2 e' he)
    rcases le_total (σ a) (g (Q.toCellScheme.grade e')) with h' | h'
    · rw [min_eq_left h'] at h
      exact h.symm
    · rw [min_eq_right h'] at h
      exact absurd h (hig.trans_le hge).ne
  -- the shifter is at least `β` at the marker, and at most `β + i`
  have hσv : (β : Label.{u}) ≤ σ v := by
    have h := heq ⟨r, hrc⟩
    change min (Q.label r) (Q.label c) = min (σ v) (g (Q.toCellScheme.grade r)) at h
    have h' : (β : Label.{u}) ≤ min (Q.label r) (Q.label c) := le_min (hβle hr.1) (hβle hc.2.1)
    rw [h] at h'
    exact h'.trans (min_le_left _ _)
  have hva : v ≤ a := by
    have h := hr.2.2 e' he hec
    rwa [hrowr, hrowe] at h
  have hσva : σ v ≤ ((β + i : Ordinal.{u}) : Label.{u}) := hσa ▸ hw.monotone hva
  -- no cap: the row entry at `e` lies below `visibilityReplace N N v`
  have hcap : a < visibilityReplace N N v := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨i', hi'N, hσv'⟩ := exists_lt_eq_coe_add_natCast_of_le_of_lt hσv (hσva.trans_lt hiβN)
    have hcomm := hw.visibilityReplace_comm v N (hσva.trans hig.le) N le_rfl
    rw [hσv', visibilityReplace_coe_add_natCast hβ hi'N N] at hcomm
    have hmono : σ (visibilityReplace N N v) ≤ σ a := hw.monotone hle
    rw [hcomm, hσa] at hmono
    exact hiβN.not_ge hmono
  rw [hrowr] at hrj
  rw [hrj, visibilityReplace_coe_add hμ] at hcap
  split_ifs at hcap with hjN
  · -- the row reads `e` at `μ + j'` with `j' < N`, and the shifter gives `i = j'`
    have hμa : (μ : Label.{u}) ≤ a := (coe_le_coe_add μ j).trans (hrj ▸ hva)
    obtain ⟨j', hj'N, haj'⟩ := exists_lt_eq_coe_add_natCast_of_le_of_lt hμa hcap
    have hcomm := hw.visibilityReplace_comm a N (hσa ▸ hig.le) j' hj'N.le
    rw [hσa, haj', visibilityReplace_coe_add_natCast hμ hj'N, ← haj', hσa,
      visibilityReplace_coe_add_natCast hβ hiN] at hcomm
    rw [hei, hrowe, haj', bandMap_coe_add_natCast, min_eq_left hj'N.le, hcomm]
  · exact absurd hva (not_le.mpr (hrj ▸ hcap))

/-- **The band label is at most the label of every lift**: under the hypotheses of the fibre gap
(`StageType.IsMarker.label_eq_bandMap_or_le`), every stage type at `α` reducing to `q` is at least
`bandMap β μ N (q.rowAt c e)` at a cell `e` labelled `⊤` in `q`.  Premises as there: `β` zero or a
limit, no legality of `q`, no bound on `α`. -/
theorem IsMarker.bandMap_rowAt_le_label (hβ : IsSuccPrelimit β) {Q : StageType.{u} α m}
    (hQ : Q.reduce hβ = q) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {μ : Ordinal.{u}} {j : ℕ}
    (hμ : IsSuccPrelimit μ) (hrj : q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}))
    (he : q.label e = ⊤) (e' : Fin Q.card) (he' : (e' : ℕ) = e) :
    bandMap β μ (q.toCellScheme.grade c) (q.rowAt c e) ≤ Q.label e' :=
  (hr.label_eq_bandMap_or_le hβ hQ hc hμ hrj he e' he').elim (fun h ↦ h.ge)
    fun h ↦ (bandMap_le _).trans h

/-! ### The attained least lift -/

/-- **The attained least lift at a marker.**  Let `β` be a limit, `β + ω ≤ α`, `q` legal, `c` a
top cap of `q` of grade `N`, and `r` a marker of `c` whose row entry is `μ + j` (`μ` zero or a
limit).  The band labelling, `bandMap β μ N (q.rowAt c d)` at the cells `d` labelled `⊤` and the
label of `q` elsewhere, is the least lift labelling of `q` to `α`.  Legality, the limit `β`, and
`β + ω ≤ α` are premises of this statement: they make the band labelling a lift labelling
(`StageType.IsMarker.exists_lift`); its lower bound alone is
`StageType.IsMarker.bandMap_rowAt_le_label`. -/
theorem IsMarker.isLeast_bandLabelling (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hc : q.IsTopCap c) (hr : q.IsMarker c r) {μ : Ordinal.{u}} {j : ℕ}
    (hμ : IsSuccPrelimit μ) (hrj : q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u})) :
    IsLeast {ℓ | q.IsLiftLabelling α ℓ} fun d ↦
      if q.label d = ⊤ then bandMap β μ (q.toCellScheme.grade c) (q.rowAt c d) else q.label d := by
  refine ⟨?_, fun ℓ hℓ d ↦ ?_⟩
  · obtain ⟨μ₀, j₀, hμ₀, hrj₀, Q₀, hQ₀, hQ₀l⟩ := hr.exists_lift hβ hα hq hc
    obtain ⟨rfl, -⟩ := (add_natCast_eq_add_natCast_iff hμ hμ₀).mp
      (WithTop.coe_injective (WithBot.coe_injective (hrj.symm.trans hrj₀)))
    refine (isLiftLabelling_iff hβ.isSuccPrelimit).mpr ⟨Q₀, hQ₀, fun d d' hdd' ↦ ?_⟩
    by_cases hd : q.label d = ⊤
    · rw [ite_eq_left hd]
      exact hQ₀l d d' hdd' hd
    · rw [ite_eq_right hd]
      have hlift : q.IsLiftLabelling α fun x : Fin q.card ↦
          Q₀.label ⟨x, lt_of_lt_of_eq x.2 (card_eq_of_reduce_eq hQ₀)⟩ :=
        (isLiftLabelling_iff hβ.isSuccPrelimit).mpr
          ⟨Q₀, hQ₀, fun x x' hxx' ↦ congrArg Q₀.label (Fin.ext hxx')⟩
      exact (congrArg Q₀.label (Fin.ext hdd')).trans (hlift.eq_label_of_ne_top hd)
  · change (if q.label d = ⊤ then _ else q.label d) ≤ ℓ d
    by_cases hd : q.label d = ⊤
    · rw [ite_eq_left hd]
      obtain ⟨Q, hQ, hQl⟩ := (isLiftLabelling_iff hβ.isSuccPrelimit).mp hℓ
      set d' : Fin Q.card := ⟨d, lt_of_lt_of_eq d.2 (card_eq_of_reduce_eq hQ)⟩
      rw [← hQl d d' rfl]
      exact hr.bandMap_rowAt_le_label hβ.isSuccPrelimit hQ hc hμ hrj hd d' rfl
    · rw [ite_eq_right hd, hℓ.eq_label_of_ne_top hd]

/-- **The attained least lift.**  For `β` a limit and `β + ω ≤ α`, every legal stage type `q` at
`β` has a least lift labelling to `α`: one lawful labelling of the cells of `q`, reducing to `q`,
at most every lift labelling at every cell.  Legality, the limit `β`, and `β + ω ≤ α` are premises
of the statement. -/
theorem exists_isLeast_isLiftLabelling (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal) :
    ∃ ℓ₀, IsLeast {ℓ | q.IsLiftLabelling α ℓ} ℓ₀ := by
  by_cases htf : q.IsTopFree
  · refine ⟨q.label, ⟨q.isLawful, fun d ↦ (q.atStage d).mono (le_self_add.trans hα),
      fun d ↦ (q.atStage d).reduce_eq⟩, fun ℓ hℓ d ↦ (hℓ.eq_label_of_ne_top (htf d)).ge⟩
  obtain ⟨c, hc⟩ := exists_isTopCap hq htf
  obtain ⟨r, hr⟩ := exists_isMarker hc.2.1
  obtain ⟨μ, j, hμ, hrj, -⟩ := hr.exists_lift hβ hα hq hc
  exact ⟨_, hr.isLeast_bandLabelling hβ hα hq hc hμ hrj⟩

/-! ### Forcing read by the least lift -/

/-- A cell of `q` transported from a cell of the root labelled `⊤` is labelled `⊤`. -/
theorem label_eq_top_of_restrictFace {f : Fin k ↪ Fin m} {p : StageType.{u} β k}
    {d : Fin p.card} (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    q.label e = ⊤ := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hfp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β k ↦ s.card) hqp
  set i₀ : Fin (q.toScheme.comap f).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  rw [← he i₀ rfl]
  exact label_cellMap_eq_top hfp hd i₀ rfl

/-- **Forcing is forcing at every lift**: if `q` restricts to `p` along `f` and `e` is the cell of
`q` transported from the cell `d` of `p`, then `(q, f)` forces `n` at `d` exactly when every stage
type at `α` reducing to `q` is at least `β + n` at the position of `e`. -/
theorem forcesThreshold_iff_forall_lift (hβ : IsSuccPrelimit β) {f : Fin k ↪ Fin m}
    {p : StageType.{u} β k} {d : Fin p.card} (hfp : restrictFace f q = some p)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) {n : ℕ} :
    ForcesThreshold α hβ q f p d n ↔ ∀ (Q : StageType.{u} α m) (e' : Fin Q.card),
      Q.reduce hβ = q → (e' : ℕ) = e → ((β + n : Ordinal.{u}) : Label.{u}) ≤ Q.label e' := by
  refine ⟨fun hforce Q e' hQ he' ↦ ?_, fun h ↦ ⟨hfp, fun Q P hQ hP i hi ↦ ?_⟩⟩
  · obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hfp
    have hcard : (q.comap f hf).card = p.card :=
      congrArg (fun s : StageType.{u} β k ↦ s.card) hqp
    set i₀ : Fin (q.comap f hf).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
    have hie : q.cellMap f i₀ = e := he i₀ rfl
    subst hQ
    have hf' : univ.map f ∈ Q.toCellScheme.faces := hf
    have h := hforce.2 Q (Q.comap f hf') rfl (restrictFace_of_mem Q f hf') i₀ rfl
    -- the label of the face of `Q` at `i₀` is the label of `Q` at the transported cell
    change ((β + n : Ordinal.{u}) : Label.{u}) ≤ Q.label (Q.cellMap f i₀) at h
    have hpos : Q.cellMap f i₀ = e' := Fin.ext (by rw [he']; exact congrArg Fin.val hie)
    rwa [hpos] at h
  · subst hQ
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff Q f).mp hP
    rw [comap_label]
    exact h Q _ rfl (congrArg Fin.val (he i hi))

/-- **Forcing is read by any least lift.**  Let `β` be zero or a limit, `q` restrict to `p` along
`f`, `e` be the cell of `q` transported from the cell `d` of `p`, and `ℓ₀` be a least lift labelling
of `q` to `α`.  Then `(q, f)` forces `n` at `d` exactly when `β + n ≤ ℓ₀ e`.  No other premise is
used: no legality, no bound on `α`, no top cap or marker, and no hypothesis on the label of `d`.
Legality, a limit `β`, and `β + ω ≤ α` give the existence of `ℓ₀`
(`StageType.exists_isLeast_isLiftLabelling`). -/
theorem forcesThreshold_iff_coe_add_le_of_isLeast (hβ : IsSuccPrelimit β) {f : Fin k ↪ Fin m}
    {p : StageType.{u} β k} {d : Fin p.card} (hfp : restrictFace f q = some p)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e)
    {ℓ₀ : Fin q.card → Label.{u}} (hleast : IsLeast {ℓ | q.IsLiftLabelling α ℓ} ℓ₀) {n : ℕ} :
    ForcesThreshold α hβ q f p d n ↔ ((β + n : Ordinal.{u}) : Label.{u}) ≤ ℓ₀ e := by
  rw [forcesThreshold_iff_forall_lift hβ hfp he]
  refine ⟨fun h ↦ ?_, fun h Q e' hQ he' ↦ ?_⟩
  · obtain ⟨Q₀, hQ₀, hQ₀l⟩ := (isLiftLabelling_iff hβ).mp hleast.1
    set e₀ : Fin Q₀.card := ⟨e, lt_of_lt_of_eq e.2 (card_eq_of_reduce_eq hQ₀)⟩
    rw [← hQ₀l e e₀ rfl]
    exact h Q₀ e₀ hQ₀ rfl
  · -- the labels of `Q`, read on the cells of `q`, form a lift labelling, which is above `ℓ₀`
    have hlift : q.IsLiftLabelling α fun x : Fin q.card ↦
        Q.label ⟨x, lt_of_lt_of_eq x.2 (card_eq_of_reduce_eq hQ)⟩ :=
      (isLiftLabelling_iff hβ).mpr ⟨Q, hQ, fun x x' hxx' ↦ congrArg Q.label (Fin.ext hxx')⟩
    exact (h.trans (hleast.2 hlift e)).trans_eq (congrArg Q.label (Fin.ext he'.symm))

/-- **Forcing is read by the band label.**  Let `β` be a limit, `β + ω ≤ α`, `q` a legal stage
type at `β` restricting to `p` along `f`, `c` a top cap of `q` of grade `N`, and `r` a marker of `c`
whose row entry is `μ + j` (`μ` zero or a limit).  At a cell `d` of `p` labelled `⊤`, transported
to the cell `e` of `q`, `(q, f)` forces `n` exactly when `β + n ≤ bandMap β μ N (q.rowAt c e)`, the
label at `e` of the least lift. -/
theorem IsMarker.forcesThreshold_iff_coe_add_le_bandMap (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {μ : Ordinal.{u}} {j : ℕ}
    (hμ : IsSuccPrelimit μ) (hrj : q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}))
    {f : Fin k ↪ Fin m} {p : StageType.{u} β k} {d : Fin p.card}
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) {n : ℕ} :
    ForcesThreshold α hβ.isSuccPrelimit q f p d n ↔
      ((β + n : Ordinal.{u}) : Label.{u}) ≤
        bandMap β μ (q.toCellScheme.grade c) (q.rowAt c e) := by
  have hel := label_eq_top_of_restrictFace hfp hd he
  rw [forcesThreshold_iff_forall_lift hβ.isSuccPrelimit hfp he]
  refine ⟨fun h ↦ ?_, fun h Q e' hQ he' ↦
    h.trans (hr.bandMap_rowAt_le_label hβ.isSuccPrelimit hQ hc hμ hrj hel e' he')⟩
  obtain ⟨Q₀, hQ₀, hQ₀l⟩ := (isLiftLabelling_iff hβ.isSuccPrelimit).mp
    (hr.isLeast_bandLabelling hβ hα hq hc hμ hrj).1
  set e₀ : Fin Q₀.card := ⟨e, lt_of_lt_of_eq e.2 (card_eq_of_reduce_eq hQ₀)⟩
  have h₀ := h Q₀ e₀ hQ₀ rfl
  rwa [hQ₀l e e₀ rfl, ite_eq_left hel] at h₀

/-- **Forcing is read by the rows**, both ways.  Under the hypotheses of
`StageType.IsMarker.forcesThreshold_iff_coe_add_le_bandMap`, with no decomposition of the row entry
at the marker given, `(q, f)` forces `n` at `d` exactly when `n ≤ N` and
`visibilityReplace N n (q.rowAt c r) ≤ q.rowAt c e`.  The forward implication is
`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`; the converse is the leastness
of the band lift. -/
theorem IsMarker.forcesThreshold_iff_le_grade_and_visibilityReplace_rowAt_le (hβ : IsSuccLimit β)
    (hα : β + ω ≤ α) (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r)
    {f : Fin k ↪ Fin m} {p : StageType.{u} β k} {d : Fin p.card}
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) {n : ℕ} :
    ForcesThreshold α hβ.isSuccPrelimit q f p d n ↔ n ≤ q.toCellScheme.grade c ∧
      visibilityReplace (q.toCellScheme.grade c) n (q.rowAt c r) ≤ q.rowAt c e := by
  refine ⟨fun h ↦ h.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr hd he,
    fun ⟨hn, hvis⟩ ↦ ?_⟩
  obtain ⟨μ, j, hμ, hrj, -⟩ := hr.exists_lift hβ hα hq hc
  have hel := label_eq_top_of_restrictFace hfp hd he
  have hre : q.rowAt c r ≤ q.rowAt c e := hr.2.2 e hel (hc.mem_below hel)
  rw [hrj] at hre hvis
  exact (hr.forcesThreshold_iff_coe_add_le_bandMap hβ hα hq hc hμ hrj hfp hd he).mpr
    (coe_add_le_bandMap_of_visibilityReplace_le hμ hn hre hvis)

/-! ### The provisional offset is the offset of the least lift -/

/-- **The provisional offset is read by the least lift.**  Under the hypotheses of
`StageType.IsMarker.forcesThreshold_iff_coe_add_le_bandMap`, the label of the provisional offset of
`d` at `(q, f)` is the band label `bandMap β μ N (q.rowAt c e)`: the provisional offset is the
offset above `β` of the least lift at `e`. -/
theorem IsMarker.ofOffset_provisionalOffset (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {μ : Ordinal.{u}} {j : ℕ}
    (hμ : IsSuccPrelimit μ) (hrj : q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}))
    {f : Fin k ↪ Fin m} {p : StageType.{u} β k} {d : Fin p.card}
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    Label.ofOffset β (provisionalOffset α hβ.isSuccPrelimit q f p d) =
      bandMap β μ (q.toCellScheme.grade c) (q.rowAt c e) := by
  set N := q.toCellScheme.grade c
  have hel := label_eq_top_of_restrictFace hfp hd he
  have hre : ((μ + j : Ordinal.{u}) : Label.{u}) ≤ q.rowAt c e :=
    hrj ▸ hr.2.2 e hel (hc.mem_below hel)
  -- the band label is `β + o` with `o ≤ N`
  obtain ⟨o, -, ho⟩ := exists_lt_eq_coe_add_natCast_of_le_of_lt (o := β) (N := N + 1)
    (coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le hre).ne')
    ((bandMap_le _).trans_lt (lt_of_not_ge fun h ↦
      (Nat.lt_succ_self N).not_ge (coe_add_natCast_le_coe_add_natCast_iff.mp h)))
  have key (n : ℕ) : ForcesThreshold α hβ.isSuccPrelimit q f p d n ↔ n ≤ o := by
    rw [hr.forcesThreshold_iff_coe_add_le_bandMap hβ hα hq hc hμ hrj hfp hd he, ho,
      coe_add_natCast_le_coe_add_natCast_iff]
  have hoff : provisionalOffset α hβ.isSuccPrelimit q f p d = o :=
    le_antisymm (iSup₂_le fun n hn ↦ Nat.cast_le.mpr ((key n).mp hn))
      ((key o).mpr le_rfl).le_provisionalOffset
  rw [hoff, Label.ofOffset_natCast, ho]

/-- Under the hypotheses of `StageType.IsMarker.ofOffset_provisionalOffset`, the provisional offset
is finite and at most the grade of the top cap. -/
theorem IsMarker.provisionalOffset_le_grade (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {f : Fin k ↪ Fin m}
    {p : StageType.{u} β k} {d : Fin p.card} (hfp : restrictFace f q = some p)
    (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    provisionalOffset α hβ.isSuccPrelimit q f p d ≤ q.toCellScheme.grade c := by
  refine iSup₂_le fun n hn ↦ Nat.cast_le.mpr ?_
  exact ((hr.forcesThreshold_iff_le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hfp hd
    he).mp hn).1

end StageType

end VaughtConjecture

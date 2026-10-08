/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryFullCap
import VaughtConjecture.Extension.OrbitCode

/-!
# The row of the cap reads every reference cell at its finite part

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)); semantic contract, item 8.

`VaughtConjecture.Continuation.StableRecoveryFullCap` reduces stable recovery schemes for the graded
cap calibration to cap-reading extensions (`StageType.HasCapReadingExtensions`, open): legal
extensions whose cells at the graded face `(univ, N)` read the new cells of the coface `D`
through a full-scope cap of grade `N` (`StageType.ReadsThroughCap`).  The instances compiled so far
designed the context and the reading rows together.  This file removes that design from the
reading clause: the cap's own row is a reading row, at every legal `T⁺`.  Each item below is
compiled in this repository (theorem named), unless marked otherwise.

**The finite part at a reference cell** (`Label.TransformsTo.exists_eq_omega0_mul_add`, in
`VaughtConjecture.Label.Transform`; `StageType.exists_row_eq_omega0_mul_add`, in
`VaughtConjecture.Stage.Basic`).  Let a lawful section `p` have a cell `b` of grade `N`
(the cap) and a cell `a` below it with `p a = μ + i`, `μ` zero or a limit, `i < N` and
`μ + i < p b`.  Then the row of `b` reads `a` at `ω · c + i` for some ordinal `c`: the same finite
part.  Locality at `b` gives a witness `(g, σ)` with `g N ≥ p b`, so `σ` sends the value at `a` to
`μ + i`; commuting with visibility replacement at the threshold `N` excludes `⊥`, `⊤` and every
finite part at least `N`, and fixes the finite part `i`.

**One code per block** (`Label.TransformsTo.eq_of_eq_omega0_mul_add`, in
`VaughtConjecture.Label.Transform`; `StageType.eq_of_row_eq_omega0_mul_add`, in
`VaughtConjecture.Stage.Basic`).  Two such cells of one block `μ` are read in one block
`ω · c`: the shifter sends `ω · c + j` to `μ + j` for every `j ≤ N`, and a strictly larger code
`c'` would send `ω · c'` to `μ` below `σ (ω · c + N) = μ + N`.  So the row of the cap defines a
code of the blocks of its reference cells (`StageType.capBlockCode`), and the **cap code** of a
label (`StageType.capCode`): `⊥` for `⊥`, the cap's value at itself for `⊤`, and
`ω · capBlockCode μ + n` for `μ + n` (`StageType.row_eq_capBlockCode`, `StageType.capCode_coe_add`).

**The cap row reads through the cap** (`StageType.readsThroughCap_of_capRow`).  Let `T⁺` be a
stage type at `λ_{ξ+1}`, `b` a full-scope graded cap of `T⁺` for `D` and `γ`
(`StageType.IsGradedCap`), and `E` a scheme on one more point with face `T⁺` along the first
points.  A cell `u` of `E` above the cap whose row agrees with the cap's row of `T⁺` on the cells
of that face and reads a new cell `e` at the cap code of a label `ℓ` of `D` reads `e` through the
cap as a cell labelled `ℓ`.  The reference cell is the one given by the calibration, read by the
cap row at its finite part; the code of its block is the cap code of `ℓ`.  No context is designed:
the statement holds for every legal `T⁺`, every full-scope graded cap and every scheme `E`.

**Cap-row extensions** (`StageType.IsCapRowExtension`, `StageType.HasCapRowExtensions`, a new
named statement, open).  A cap-row extension is a legal scheme `E` with the faces `T⁺` and `D` in
which every cell at `(univ, N)` agrees with the cap row on the old cells and reads every new cell
of `D` at the cap code of its label.  It is a cap-reading extension
(`StageType.IsCapRowExtension.isCapReadingExtension`), so `StageType.HasCapRowExtensions ξ` implies
`StageType.HasCapReadingExtensions ξ` (`StageType.HasCapRowExtensions.hasCapReadingExtensions`).
It prescribes the whole row at `(univ, N)` on the old cells, so it is stronger than needed: the
reading needs only the reference cells read in the block of their new cells.  Whether the cap row
on the old cells always extends to a lawful row at `(univ, N)` is not known (argued, not
formalized: on the face of `D` the block codes of the cap row need room for the values of the
donor's locality witnesses; the coded copy of the capped labels has that room by construction).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

namespace Label

/-- The block index (`Label.blockIndex`: `o / ω` at an ordinal `o`, `0` at `⊥` and `⊤`) of
`ω · c + i` is `c`: the code `c` of a value `ω · c + i`. -/
theorem blockIndex_omega0_mul_add (c : Ordinal.{u}) (i : ℕ) :
    blockIndex ((ω * c + i : Ordinal.{u}) : Label.{u}) = c :=
  omega0_mul_add_natCast_div c i

end Label

/-! ### The row of the cap -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

open Classical in
/-- The **block code of the cap** for a block `μ`: the block index of the value of the row of the
cap `b` at some cell below `b` labelled `μ + i`, with `i` below the grade of `b` and `μ + i`
below the label of `b`, if there is one, and `0` otherwise.  It does not depend on the cell
(`StageType.row_eq_capBlockCode`). -/
noncomputable def capBlockCode (T : StageType.{u} α n) (b : Fin T.card) (μ : Ordinal.{u}) :
    Ordinal.{u} :=
  if h : ∃ (a : T.toCellScheme.below (T.toCellScheme.gradedIndex b)) (i : ℕ),
      T.label a = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i < T.toCellScheme.grade b ∧
        ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b
  then blockIndex (T.rows.row b h.choose) else 0

/-- **The cap row reads every reference cell at the cap's block code**: for a cell `a` below the
cap `b` labelled `μ + i` (`μ` zero or a limit), with `i` below the grade of `b` and `μ + i` below
the label of `b`, the row of `b` reads `a` at `ω · capBlockCode μ + i`. -/
theorem row_eq_capBlockCode (T : StageType.{u} α n) {a b : Fin T.card}
    (ha : a ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b)) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {i : ℕ} (hi : i < T.toCellScheme.grade b)
    (hTa : T.label a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hab : ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b) :
    T.rows.row b ⟨a, ha⟩ = ((ω * T.capBlockCode b μ + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨c, hc⟩ := T.exists_row_eq_omega0_mul_add ha hμ hi hTa hab
  have hex : ∃ (a : T.toCellScheme.below (T.toCellScheme.gradedIndex b)) (i : ℕ),
      T.label a = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i < T.toCellScheme.grade b ∧
        ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b := ⟨⟨a, ha⟩, i, hTa, hi, hab⟩
  rw [capBlockCode, dite_eq_left hex]
  obtain ⟨i', hTa', hi', ha'b⟩ := hex.choose_spec
  obtain ⟨c', hc'⟩ := T.exists_row_eq_omega0_mul_add hex.choose.2 hμ hi' hTa' ha'b
  rw [hc', blockIndex_omega0_mul_add, hc,
    T.eq_of_row_eq_omega0_mul_add ha hex.choose.2 hμ hi hi' hTa hTa' hab ha'b hc hc']

/-- The **cap code** of a label for the cap `b`: `⊥` at `⊥`; the value of the row of `b` at `b`
itself at the formal top; and at an ordinal `μ + n` (`μ` zero or a limit), `ω · c + n` for the
block code `c = capBlockCode μ` of the cap. -/
noncomputable def capCode (T : StageType.{u} α n) (b : Fin T.card) : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥
    (fun o ↦ ((ω * T.capBlockCode b (ω * (o / ω)) + o % ω : Ordinal.{u}) : Label.{u}))
    (T.rows.row b ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩)

/-- The cap code of `⊥` is `⊥`. -/
@[simp] theorem capCode_bot (T : StageType.{u} α n) (b : Fin T.card) : T.capCode b ⊥ = ⊥ := rfl

/-- The cap code of the formal top is the value of the row of the cap at itself. -/
@[simp] theorem capCode_top (T : StageType.{u} α n) (b : Fin T.card) :
    T.capCode b ⊤ = T.rows.row b ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩ := rfl

/-- The cap code of `μ + n`, for `μ` zero or a limit: `ω · capBlockCode μ + n`. -/
theorem capCode_coe_add (T : StageType.{u} α n) (b : Fin T.card) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) (k : ℕ) :
    T.capCode b ((μ + k : Ordinal.{u}) : Label.{u}) =
      ((ω * T.capBlockCode b μ + k : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨c, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ
  -- the cap code at an ordinal, unfolded
  change ((ω * T.capBlockCode b (ω * ((ω * c + k) / ω)) + (ω * c + k) % ω : Ordinal.{u}) :
    Label.{u}) = _
  rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 k),
    add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (natCast_lt_omega0 k)]

/-! ### The cap row reads through the cap -/

section CapRow

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- Equal schemes have equal scopes at cells with equal positions. -/
private theorem scope_congr {S S' : Scheme.{u} m} (h : S = S') {i : Fin S.card}
    {j : Fin S'.card} (hij : (i : ℕ) = j) : S.toCellScheme.scope i = S'.toCellScheme.scope j := by
  subst h
  rw [Fin.ext hij]

/-- **The cap row reads through the cap.**  Let `b₀` be a graded cap of full scope of `T⁺` for `D`
and `γ` (`StageType.IsGradedCap`), and let `E` be a scheme on one more point whose face along the
first points is the scheme of `T⁺`, with `b` the cell of that face at the position of `b₀`.  Let
the row of a cell `u` of `E` agree with the row of the cap `b₀` of `T⁺` on the cells of that face
below `u`, and read a cell `e` at the cap code (`StageType.capCode`) of the label of a cell `j` of
`D`.  Then `u` reads `e` through the cap as a cell labelled `D.label j`
(`StageType.ReadsThroughCap`).  The reference cell is the one of the calibration: the cap row reads
it at its finite part, in the block of the cap code (`StageType.row_eq_capBlockCode`). -/
theorem readsThroughCap_of_capRow {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {b₀ : Fin Tp.card}
    (hbu : Tp.toCellScheme.scope b₀ = univ) (hcap : IsGradedCap ξ Tp D γ b₀)
    {E : Scheme.{u} (m + 1)} (hT : E.comap Fin.castSuccEmb = Tp.toScheme)
    {b : Fin (E.comap Fin.castSuccEmb).card} (hbb₀ : (b : ℕ) = b₀) {u e : Fin E.card}
    (hold : ∀ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card), (a : ℕ) = a₀ →
      ∀ (ha : E.cellMap Fin.castSuccEmb a ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
        (ha₀ : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b₀)),
        E.rows.row u ⟨_, ha⟩ = Tp.rows.row b₀ ⟨a₀, ha₀⟩)
    (j : Fin D.card)
    (hnew : ∀ he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u),
      E.rows.row u ⟨e, he⟩ = Tp.capCode b₀ (D.label j)) :
    Tp.ReadsThroughCap E b u e (D.label j) := by
  obtain ⟨hb₀, -, -, href⟩ := hcap
  have hcard : (E.comap Fin.castSuccEmb).card = Tp.card := congrArg Scheme.card hT
  have hgb : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) = Tp.toCellScheme.grade b₀ :=
    Scheme.grade_congr hT hbb₀
  have hscb : E.toCellScheme.scope (E.cellMap Fin.castSuccEmb b) =
      univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
    rw [← Scheme.map_comap_scope, scope_congr hT hbb₀, hbu]
  intro he hb
  refine ⟨fun h ↦ by rw [hnew he, h, capCode_bot], fun h ↦ ?_, fun μ n hμ h ↦ ?_⟩
  · rw [hnew he, h, capCode_top, hold b b₀ hbb₀ hb]
  -- the reference cell of the calibration, in the block `μ`
  obtain ⟨μ', n', i, a₀, hμ', ho, hn, hi, ha₀N, ha₀⟩ := href j (μ + n) h
  obtain ⟨rfl, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ hμ').mp ho
  -- the block `μ` is at most `λ_ξ`, since the label of `D` lies below `λ_{ξ+1}`
  have hlt : μ + n < blockStage ξ + ω := by
    rcases D.atStage j with h' | h'
    · rw [h, blockStage_add_one] at h'
      exact_mod_cast h'
    · rw [h] at h'
      exact absurd h' (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  have hμξ : μ ≤ blockStage ξ := by
    by_contra hμξ
    exact (add_omega0_le_of_isSuccPrelimit hμ (not_le.mp hμξ)).not_gt
      ((le_self_add).trans_lt hlt)
  -- the reference value lies below the cap
  have hab : ((μ + i : Ordinal.{u}) : Label.{u}) < Tp.label b₀ := by
    refine lt_of_lt_of_le ?_ hb₀
    have : μ + i < blockStage ξ + Tp.toCellScheme.grade b₀ := by
      rcases hμξ.lt_or_eq with hμξ | rfl
      · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt hμξ i).trans_le le_self_add
      · exact add_lt_add_right (Nat.cast_lt.mpr hi) _
    exact_mod_cast this
  have ha₀b : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b₀) := by
    refine ⟨?_, ha₀N⟩
    -- the scope of `b₀` is all the points of `T⁺`
    change Tp.toCellScheme.scope a₀ ⊆ Tp.toCellScheme.scope b₀
    rw [hbu]
    exact subset_univ _
  -- the reference cell in the face of `E`, below `u`
  set a : Fin (E.comap Fin.castSuccEmb).card := Fin.cast hcard.symm a₀
  have ha : E.cellMap Fin.castSuccEmb a ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u) := by
    refine ⟨?_, ?_⟩
    · -- the scope of the reference cell lies in that of the cap, of full scope
      change E.toCellScheme.scope (E.cellMap Fin.castSuccEmb a) ⊆ _
      rw [← Scheme.map_comap_scope]
      exact (map_subset_map.mpr (subset_univ _)).trans (hscb ▸ hb.1)
    · exact (Scheme.grade_congr hT rfl).trans_le (ha₀N.trans (hgb.symm.trans_le hb.2))
  refine ⟨hgb ▸ hn, a, a₀, i, Tp.capBlockCode b₀ μ, rfl, ha₀, hgb ▸ hi, ha, ?_, ?_⟩
  · rw [hold a a₀ rfl ha ha₀b, Tp.row_eq_capBlockCode ha₀b hμ hi ha₀ hab]
  · rw [hnew he, h, capCode_coe_add _ _ hμ]

/-- A **cap-row extension** of `T⁺` along `f` for `D` and a cell `b` of `T⁺` of grade `N`: a legal
scheme `E` on `m + 1` points with the faces of a cap-reading extension
(`StageType.IsCapReadingExtension`) in which every cell `u` at the graded face `(univ, N)`

* agrees with the row of the cap `b` of `T⁺` on the cells of the face along the first points below
  it; and
* reads every new cell of `D` (a cell whose scope contains the new point) at the cap code
  (`StageType.capCode`) of its label. -/
def IsCapRowExtension {α : Ordinal.{u}} (Tp : StageType.{u} α m) (f : Fin k ↪ Fin m)
    (D : StageType.{u} α (k + 1)) (b : Fin Tp.card) (E : Scheme.{u} (m + 1)) : Prop :=
  E.IsLegal ∧ univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces ∧
    E.comap Fin.castSuccEmb = Tp.toScheme ∧ univ.map (extendByLast f) ∈ E.toCellScheme.faces ∧
    E.comap (extendByLast f) = D.toScheme ∧
    ∀ u, E.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b) →
      (∀ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card), (a : ℕ) = a₀ →
        ∀ (ha : E.cellMap Fin.castSuccEmb a ∈
            E.toCellScheme.below (E.toCellScheme.gradedIndex u))
          (ha₀ : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b)),
          E.rows.row u ⟨_, ha⟩ = Tp.rows.row b ⟨a₀, ha₀⟩) ∧
      ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
        Fin.last k ∈ D.toCellScheme.scope j →
        ∀ he : E.cellMap (extendByLast f) i ∈
            E.toCellScheme.below (E.toCellScheme.gradedIndex u),
          E.rows.row u ⟨_, he⟩ = Tp.capCode b (D.label j)

/-- **A cap-row extension for a full-scope graded cap is a cap-reading extension**
(`StageType.readsThroughCap_of_capRow` at every cell of `(univ, N)` and every new cell of `D`). -/
theorem IsCapRowExtension.isCapReadingExtension {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {b : Fin Tp.card} (hbu : Tp.toCellScheme.scope b = univ) (hcap : IsGradedCap ξ Tp D γ b)
    {E : Scheme.{u} (m + 1)} (h : IsCapRowExtension Tp f D b E) :
    IsCapReadingExtension Tp f D b E := by
  obtain ⟨hE, hc, hcT, hf, hED, hrow⟩ := h
  have hcard : (E.comap Fin.castSuccEmb).card = Tp.card := congrArg Scheme.card hcT
  exact ⟨hE, hc, hcT, hf, hED, Fin.cast hcard.symm b, rfl, fun u hu i j hij hj ↦
    readsThroughCap_of_capRow hbu hcap hcT rfl (hrow u hu).1 j ((hrow u hu).2 i j hij hj)⟩

variable (ξ) in
/-- **Cap-row extensions at `ξ`** (a new named statement; open): `StageType.HasCapReadingExtensions`
with the cap-row extension (`StageType.IsCapRowExtension`) in place of the cap-reading extension.
For every legal `T⁺` at `λ_{ξ+1}`, embedding `f` of `k > 0` points with face `P`, coface `D` of
`P`, `γ < λ_{ξ+1}` and full-scope graded cap `b` of `T⁺` for `D` and `γ`, there is a cap-row
extension.  It prescribes the rows at `(univ, N)` on all the old cells, so it is stronger than
`StageType.HasCapReadingExtensions`; whether such rows are always lawful is not known. -/
def HasCapRowExtensions : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      ∀ b : Fin Tp.card, Tp.toCellScheme.scope b = univ → IsGradedCap ξ Tp D γ b →
        ∃ E : Scheme.{u} (m + 1), IsCapRowExtension Tp f D b E

/-- **Cap-row extensions give cap-reading extensions**
(`StageType.IsCapRowExtension.isCapReadingExtension`).  Both statements are open; this is the
implication only. -/
theorem HasCapRowExtensions.hasCapReadingExtensions (h : HasCapRowExtensions ξ) :
    HasCapReadingExtensions ξ := by
  intro m k Tp f P hT hk hP D hD γ hγ b hbu hcap
  obtain ⟨E, hE⟩ := h Tp f P hT hk hP D hD γ hγ b hbu hcap
  exact ⟨E, hE.isCapReadingExtension hbu hcap⟩

end CapRow

end StageType

end VaughtConjecture

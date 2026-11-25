/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanRankGlue

/-!
# The restricted rank glue at the grade one

Process rank `ω₁`, the finite span of mutual rigidity: proof of
`ProcessRank.RestrictedRankGlueTarget` (`ProcessRank.restrictedRankGlue`).

**New values.**  The prescribed side is the one-sided capped lift of the old values `F ∘ a` at
the grade one with no admission (`ProcessRank.oneSidedStateLift` with no designated cells).  The
other side is chosen on the **ranks**, with `m(a)` the largest undesignated rank:

1. `ℓ ≤ m(a)` (equality included): the other side capped at `c`;
2. `m(a) < ℓ` and `a` inactive (or `K > 1`): the other side kept;
3. `m(a) < ℓ`, `K ≤ 1` and `a` separated: the high tail of the prescribed side grafted onto the
   other side (`Scheme.graftHighTail`), the two sides having the same high set since the
   designated ranks agree.

The new values `P'` agree with `F ∘ a` capped at `c`, so a field is **low** (`P' x < c`) exactly
when its old rank is below `ℓ` (`ProcessRank.lt_iff_lt`).

**New ranks and table** (`ProcessRank.glueRanks`, `ProcessRank.glueTable`).  A low field keeps its
old rank **literally**, also where the old table repeats a value (a plateau of `F`); a high field
gets `ℓ - 1` plus the rank of its new value among the new values at least `c`
(`Label.valueRank`).  The new table is `F` below `ℓ`, and above it the value table of the new high
values, shifted to start at `ℓ`; it is `F` everywhere if no new value at least `c` is other than
`⊥`.

* **Height** (`ProcessRank.sub_one_add_valueRank_le_card`, `ProcessRank.glueRanks_le`): the ranks
  `1, …, ℓ - 1` are occupied by low fields (density of the old ranks below a high field), and the
  distinct new high values by the high fields, so `ℓ - 1 + valueRank ≤ 2 |S| ≤ H`.
* **Literal low ranks and the table below `ℓ`** (`ProcessRank.glueRanks_of_lt`,
  `ProcessRank.min_glueRanks`, `ProcessRank.glueTable_of_lt`), and the new table reads the new
  ranks as the new values (`ProcessRank.glueTable_glueRanks`), which gives the capped agreement and
  the literal prescription.
* **Lawful tables** (`ProcessRank.hasLawfulTables_glueRanks`): order interpolation
  (`Scheme.hasLawfulTables_of_order`) against the new values; the order property of the new ranks
  comes from that of the old ranks at a low middle field and from that of the new values at a high
  one (`ProcessRank.min_glueRanks_le_min`); the order property and availability of the old ranks
  are read off their lawful tables at the strictly increasing table `ProcessRank.natTable`.
* **Positive table** (`ProcessRank.isPositiveTable_glueTable`) and **density**
  (`ProcessRank.glueRanks_dense`).
* **Admission** of the new ranks: in case 1 an undesignated field of old rank `m(a) ≥ ℓ` is high
  and the capped designated fields of the other side are at most `c`; in case 2 the undesignated
  and the low designated ranks are kept, so separation of the new ranks would separate `a`; in
  case 3 the two copies of a designated cell have equal new values (high) or equal old ranks (low).

The special cases are covered by the general argument: at the cap `⊥` the first rank `ℓ` is `0`
(`ProcessRank.eq_bot_iff_eq_zero`), every field is high and the new ranks are the value ranks of the
new values; with no field at least `c` the new ranks and table are the old ones below `ℓ` and the
table is `F`; at a plateau of `F` below `ℓ` the distinct old ranks are kept; unused entries above
the occupied ranks repeat the largest new value (the value table is constant there).
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label

/-! ### New ranks and tables from new values -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- The values of `P'` at least `c`, and `⊥` elsewhere. -/
noncomputable def highPart (c : Label.{u}) (P' : ι → Label.{u}) (x : ι) : Label.{u} :=
  if c ≤ P' x then P' x else ⊥

/-- **The new ranks**: the old rank `a x` at a field whose new value is below `c`; otherwise
`ℓ - 1` plus the rank of its new value among the new values at least `c`. -/
noncomputable def glueRanks (a : ι → ℕ) (ℓ : ℕ) (c : Label.{u}) (P' : ι → Label.{u}) (x : ι) :
    ℕ :=
  if P' x < c then a x else (ℓ - 1) + valueRank (highPart c P') (highPart c P' x)

/-- **The new table**: the old table below `ℓ` (and everywhere if no new value other than `⊥`
is at least `c`); otherwise the value table of the new values at least `c`, shifted to start
at `ℓ`. -/
noncomputable def glueTable (F : ℕ → Label.{u}) (ℓ : ℕ) (c : Label.{u}) (P' : ι → Label.{u})
    (i : ℕ) : Label.{u} := by
  classical
  exact if i < ℓ ∨ ∀ x, highPart c P' x = ⊥ then F i
    else valueTable (highPart c P') (i - (ℓ - 1))

variable {a : ι → ℕ} {F : ℕ → Label.{u}} {c : Label.{u}} {ℓ H : ℕ} {P' : ι → Label.{u}}

theorem glueTable_of_lt {i : ℕ} (hi : i < ℓ) : glueTable F ℓ c P' i = F i := by
  classical
  exact ite_eq_left (Or.inl hi)

omit [Fintype ι] in
theorem highPart_of_le {x : ι} (h : c ≤ P' x) : highPart c P' x = P' x := ite_eq_left h

omit [Fintype ι] in
theorem highPart_of_lt {x : ι} (h : P' x < c) : highPart c P' x = ⊥ :=
  ite_eq_right (not_le.mpr h)

omit [Fintype ι] in
/-- A value of the high part other than `⊥` is a new value at least `c`. -/
theorem le_of_highPart_ne_bot {x : ι} (h : highPart c P' x ≠ ⊥) :
    c ≤ P' x ∧ highPart c P' x = P' x := by
  by_cases hc : c ≤ P' x
  · exact ⟨hc, highPart_of_le hc⟩
  · exact absurd (highPart_of_lt (not_le.mp hc)) h

theorem glueRanks_of_lt {x : ι} (h : P' x < c) : glueRanks a ℓ c P' x = a x := ite_eq_left h

theorem glueRanks_of_le {x : ι} (h : c ≤ P' x) :
    glueRanks a ℓ c P' x = (ℓ - 1) + valueRank (highPart c P') (P' x) := by
  rw [glueRanks, ite_eq_right (not_lt.mpr h), highPart_of_le h]

/-- The nonbottom values of the high part. -/
noncomputable def highValues (c : Label.{u}) (P' : ι → Label.{u}) : Finset Label.{u} :=
  (univ.image (highPart c P')).filter (· ≠ ⊥)

/-- A value of the high part other than `⊥` has a positive rank. -/
theorem one_le_valueRank_highPart {x : ι} (hx : highPart c P' x ≠ ⊥) :
    1 ≤ valueRank (highPart c P') (highPart c P' x) :=
  Nat.one_le_iff_ne_zero.mpr fun h ↦ hx ((rankVector_eq_zero_iff (R := highPart c P') x).mp h)

/-- Some value of the high part of rank one lies below the value table at every positive rank. -/
theorem exists_le_valueTable {x : ι} (hx : highPart c P' x ≠ ⊥) {j : ℕ} (hj : 1 ≤ j) :
    ∃ e, highPart c P' e ≠ ⊥ ∧ highPart c P' e ≤ valueTable (highPart c P') j := by
  classical
  have hcard : 1 ≤ #((univ.image (highPart c P')).filter (· ≠ ⊥)) :=
    card_pos.mpr ⟨_, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ x), hx⟩⟩
  obtain ⟨e, he, he1⟩ := exists_valueRank_eq (Z := highPart c P') Nat.one_pos hcard
  refine ⟨e, he, ?_⟩
  calc highPart c P' e = valueTable (highPart c P') (valueRank (highPart c P') (highPart c P' e)) :=
        (valueTable_valueRank e).symm
    _ ≤ valueTable (highPart c P') j := monotone_valueTable (he1 ▸ hj)

/-- At a positive rank, the value table of a nonzero high part is at least `c` and not `⊥`. -/
theorem le_valueTable {x : ι} (hx : highPart c P' x ≠ ⊥) {j : ℕ} (hj : 1 ≤ j) :
    c ≤ valueTable (highPart c P') j ∧ valueTable (highPart c P') j ≠ ⊥ := by
  obtain ⟨e, he, hle⟩ := exists_le_valueTable hx hj
  exact ⟨(le_of_highPart_ne_bot he).1.trans ((le_of_highPart_ne_bot he).2 ▸ hle),
    fun h ↦ he (le_bot_iff.mp (h ▸ hle))⟩

variable (hℓF : ∀ i ≤ H, i < ℓ ↔ F i < c) (hF0 : F 0 = ⊥) (haH : ∀ x, a x ≤ H)
  (hP' : ∀ x, min (P' x) c = min (F (a x)) c)

include hℓF hF0 in
/-- The first rank reaching `c` is `0` exactly at the cap `⊥`. -/
theorem eq_bot_iff_eq_zero : c = ⊥ ↔ ℓ = 0 := by
  have h := hℓF 0 (Nat.zero_le _)
  rw [hF0] at h
  constructor
  · intro hc
    rw [hc] at h
    exact Nat.eq_zero_of_not_pos fun hl ↦ (lt_irrefl _) (h.mp hl)
  · intro hl
    rw [hl] at h
    exact not_bot_lt_iff.mp fun hb ↦ (Nat.lt_irrefl 0) (h.mpr hb)

omit [Fintype ι] in
include hℓF haH hP' in
/-- **A field is low for the new values exactly when its old rank is below `ℓ`.** -/
theorem lt_iff_lt (x : ι) : P' x < c ↔ a x < ℓ := by
  have key (p : Label.{u}) : p < c ↔ min p c < c := by
    rw [min_lt_iff, or_iff_left (lt_irrefl c)]
  have h : P' x < c ↔ F (a x) < c := by
    rw [key, hP' x, ← key]
  exact h.trans (hℓF _ (haH x)).symm

include hℓF hF0 haH hP' in
/-- **The new table reads the new ranks as the new values.** -/
theorem glueTable_glueRanks (x : ι) : glueTable F ℓ c P' (glueRanks a ℓ c P' x) = P' x := by
  classical
  by_cases hx : P' x < c
  · have hax : a x < ℓ := (lt_iff_lt hℓF haH hP' x).mp hx
    have hFx : F (a x) < c := (hℓF _ (haH x)).mp hax
    rw [glueRanks_of_lt hx, glueTable, ite_eq_left (Or.inl hax)]
    exact (eq_of_min_eq_of_lt (hP' x) hFx).symm
  · have hcx : c ≤ P' x := not_lt.mp hx
    rw [glueRanks_of_le hcx]
    by_cases hx0 : P' x = ⊥
    · have hc0 : c = ⊥ := le_bot_iff.mp (hx0 ▸ hcx)
      have hl0 : ℓ = 0 := (eq_bot_iff_eq_zero hℓF hF0).mp hc0
      rw [hx0, valueRank_bot, hl0, glueTable]
      split_ifs
      · exact hF0
      · exact valueTable_zero
    · have hhx : highPart c P' x ≠ ⊥ := by rwa [highPart_of_le hcx]
      have h1 := one_le_valueRank_highPart hhx
      rw [highPart_of_le hcx] at h1
      have hnot : ¬ ((ℓ - 1) + valueRank (highPart c P') (P' x) < ℓ ∨
          ∀ y, highPart c P' y = ⊥) := by
        rintro (h | h)
        · omega
        · exact hhx (h x)
      rw [glueTable, ite_eq_right hnot, show (ℓ - 1) + valueRank (highPart c P') (P' x) - (ℓ - 1) =
        valueRank (highPart c P') (P' x) by omega, ← highPart_of_le hcx, valueTable_valueRank]

include hℓF hF0 haH hP' in
/-- **The new ranks keep every old rank below `ℓ`.** -/
theorem min_glueRanks (x : ι) : min (a x) ℓ = min (glueRanks a ℓ c P' x) ℓ := by
  by_cases hx : P' x < c
  · rw [glueRanks_of_lt hx]
  · have hax : ℓ ≤ a x := not_lt.mp fun h ↦ hx ((lt_iff_lt hℓF haH hP' x).mpr h)
    have hcx : c ≤ P' x := not_lt.mp hx
    rw [min_eq_right hax, glueRanks_of_le hcx]
    by_cases hc0 : c = ⊥
    · rw [(eq_bot_iff_eq_zero hℓF hF0).mp hc0]
      simp
    · have hhx : highPart c P' x ≠ ⊥ := by
        rw [highPart_of_le hcx]
        exact fun h ↦ hc0 (le_bot_iff.mp (h ▸ hcx))
      have h1 := one_le_valueRank_highPart hhx
      rw [highPart_of_le hcx] at h1
      omega

include hℓF hF0 in
/-- **The new table agrees with the old one capped at `c`, up to `H`.** -/
theorem min_glueTable {i : ℕ} (hi : i ≤ H) : min (glueTable F ℓ c P' i) c = min (F i) c := by
  classical
  by_cases hc0 : c = ⊥
  · simp [hc0]
  have hl1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr fun h ↦ hc0 ((eq_bot_iff_eq_zero hℓF hF0).mpr h)
  unfold glueTable
  split_ifs with h
  · rfl
  · rw [not_or, not_forall] at h
    obtain ⟨hil, x, hx⟩ := h
    have hcF : c ≤ F i := not_lt.mp fun h' ↦ hil ((hℓF i hi).mpr h')
    have hcV := (le_valueTable hx (j := i - (ℓ - 1)) (by omega)).1
    rw [min_eq_right hcV, min_eq_right hcF]

include hℓF hF0 in
/-- **The new table is a positive table.** -/
theorem isPositiveTable_glueTable (hF : IsPositiveTable H F) (hP'1 : ∀ x, IsSelfVisible 1 (P' x))
    (hℓ : ℓ ≤ H + 1) : IsPositiveTable H (glueTable F ℓ c P') := by
  classical
  obtain ⟨hFm, -, hF1, hFpos⟩ := hF
  have hZ1 (e : ι) : IsSelfVisible 1 (highPart c P' e) := by
    unfold highPart
    split_ifs
    exacts [hP'1 e, isSelfVisible_bot 1]
  by_cases hall : ∀ x, highPart c P' x = ⊥
  · have heq : glueTable F ℓ c P' = F := funext fun i ↦ ite_eq_left (Or.inr hall)
    rw [heq]
    exact ⟨hFm, hF0, hF1, hFpos⟩
  rw [not_forall] at hall
  obtain ⟨x, hx⟩ := hall
  have hnall : ¬ ∀ y, highPart c P' y = ⊥ := fun h ↦ hx (h x)
  have hval (i : ℕ) : glueTable F ℓ c P' i =
      if i < ℓ then F i else valueTable (highPart c P') (i - (ℓ - 1)) := by
    unfold glueTable
    by_cases hi : i < ℓ
    · rw [ite_eq_left (Or.inl hi), ite_eq_left hi]
    · rw [ite_eq_right (not_or.mpr ⟨hi, hnall⟩), ite_eq_right hi]
  refine ⟨fun i j hij ↦ ?_, ?_, fun i ↦ ?_, fun i hi hiH ↦ ?_⟩
  · rw [hval, hval]
    split_ifs with hi hj hj
    · exact hFm hij
    · exact ((hℓF i (by omega)).mp hi).le.trans (le_valueTable hx (by omega)).1
    · omega
    · exact monotone_valueTable (by omega)
  · rw [hval]
    split_ifs with h0
    · exact hF0
    · rw [show (0 : ℕ) - (ℓ - 1) = 0 by omega]
      exact valueTable_zero
  · rw [hval]
    split_ifs
    exacts [hF1 i, isSelfVisible_valueTable hZ1 _]
  · rw [hval]
    split_ifs with h
    · exact hFpos i hi hiH
    · exact (le_valueTable hx (by omega)).2

include hℓF haH hP' in
/-- **The occupied-rank bound.**  At a field whose new value is at least `c`, the new rank
`ℓ - 1 + valueRank` is at most the number of fields: the ranks `1, …, ℓ - 1` are occupied by
fields with new values below `c` (by density of the old ranks, since this field has an old rank at
least `ℓ`), and the distinct new values at least `c` other than `⊥` by the other fields. -/
theorem sub_one_add_valueRank_le_card
    (hdense : ∀ i, 0 < i → ∀ x, i ≤ a x → ∃ y, a y = i) {x : ι} (hcx : c ≤ P' x) :
    (ℓ - 1) + valueRank (highPart c P') (P' x) ≤ Fintype.card ι := by
  classical
  have hvr : valueRank (highPart c P') (P' x) ≤
      #((univ.image (highPart c P')).filter (· ≠ ⊥)) := by
    rw [← highPart_of_le hcx]
    exact valueRank_le_card_values _
  set L := univ.filter fun y ↦ P' y < c with hL
  set Hi := univ.filter fun y ↦ ¬ P' y < c with hHi
  have hLH : #L + #Hi = Fintype.card ι := by rw [card_filter_add_card_filter_not, card_univ]
  have hNB : #((univ.image (highPart c P')).filter (· ≠ ⊥)) ≤ #Hi := by
    refine (card_le_card fun v hv ↦ ?_).trans (card_image_le (s := Hi) (f := P'))
    obtain ⟨hv1, hv0⟩ := mem_filter.mp hv
    obtain ⟨y, -, rfl⟩ := mem_image.mp hv1
    obtain ⟨hcy, hy⟩ := le_of_highPart_ne_bot hv0
    rw [hy]
    exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, not_lt.mpr hcy⟩)
  have hlow : ℓ - 1 ≤ #L := by
    have hax : ℓ ≤ a x := not_lt.mp fun h ↦ (not_lt.mpr hcx) ((lt_iff_lt hℓF haH hP' x).mpr h)
    have hsub : Icc 1 (ℓ - 1) ⊆ L.image a := fun i hi ↦ by
      obtain ⟨hi1, hil⟩ := mem_Icc.mp hi
      obtain ⟨y, hy⟩ := hdense i hi1 x (by omega)
      refine mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, ?_⟩, hy⟩
      exact (lt_iff_lt hℓF haH hP' y).mpr (by omega)
    have := (card_le_card hsub).trans card_image_le
    rwa [Nat.card_Icc, show ℓ - 1 + 1 - 1 = ℓ - 1 by omega] at this
  omega

include hℓF haH hP' in
/-- **The new ranks are at most `H`.** -/
theorem glueRanks_le (hcard : Fintype.card ι ≤ H)
    (hdense : ∀ i, 0 < i → ∀ x, i ≤ a x → ∃ y, a y = i) (x : ι) : glueRanks a ℓ c P' x ≤ H := by
  by_cases hx : P' x < c
  · rw [glueRanks_of_lt hx]
    exact haH x
  · rw [glueRanks_of_le (not_lt.mp hx)]
    exact (sub_one_add_valueRank_le_card hℓF haH hP' hdense (not_lt.mp hx)).trans hcard

include hℓF haH hP' in
/-- **The new ranks are dense.** -/
theorem glueRanks_dense (hdense : ∀ i, 0 < i → ∀ x, i ≤ a x → ∃ y, a y = i) :
    ∀ i, 0 < i → ∀ x, i ≤ glueRanks a ℓ c P' x → ∃ y, glueRanks a ℓ c P' y = i := by
  classical
  intro i hi x hix
  by_cases hil : i < ℓ
  · have hz : i ≤ a x := by
      by_cases hx : P' x < c
      · rwa [glueRanks_of_lt hx] at hix
      · exact hil.le.trans (not_lt.mp fun h ↦ hx ((lt_iff_lt hℓF haH hP' x).mpr h))
    obtain ⟨y, hy⟩ := hdense i hi x hz
    exact ⟨y, by rw [glueRanks_of_lt ((lt_iff_lt hℓF haH hP' y).mpr (hy ▸ hil)), hy]⟩
  · have hx : c ≤ P' x := by
      by_contra hx
      rw [glueRanks_of_lt (not_le.mp hx)] at hix
      exact hil (lt_of_le_of_lt hix ((lt_iff_lt hℓF haH hP' x).mp (not_le.mp hx)))
    rw [glueRanks_of_le hx] at hix
    have hj : 0 < i - (ℓ - 1) := by
      by_cases hl : ℓ = 0
      · omega
      · omega
    have hvr : valueRank (highPart c P') (P' x) ≤
        #((univ.image (highPart c P')).filter (· ≠ ⊥)) := by
      rw [← highPart_of_le hx]
      exact valueRank_le_card_values _
    obtain ⟨e, he, hre⟩ := exists_valueRank_eq (Z := highPart c P') hj (by omega)
    obtain ⟨hce, hee⟩ := le_of_highPart_ne_bot he
    refine ⟨e, ?_⟩
    rw [glueRanks_of_le hce, ← hee, hre]
    omega

/-- **On the fields with new values at least `c`, the new ranks follow the new values.** -/
theorem glueRanks_le_iff {x y : ι} (hx : c ≤ P' x) (hy : c ≤ P' y) :
    glueRanks a ℓ c P' x ≤ glueRanks a ℓ c P' y ↔ P' x ≤ P' y := by
  rw [glueRanks_of_le hx, glueRanks_of_le hy, Nat.add_le_add_iff_left]
  constructor
  · intro h
    rw [← highPart_of_le hx, ← highPart_of_le hy] at h ⊢
    exact le_of_valueRank_le h
  · exact fun h ↦ monotone_valueRank _ h

include hℓF haH hP' in
/-- **Low fields lie below high fields in the new ranks.** -/
theorem glueRanks_lt_of_lt_of_le {x y : ι} (hx : P' x < c) (hy : c ≤ P' y) :
    glueRanks a ℓ c P' x < glueRanks a ℓ c P' y := by
  have hax : a x < ℓ := (lt_iff_lt hℓF haH hP' x).mp hx
  have hc0 : c ≠ ⊥ := ne_bot_of_gt hx
  have hhy : highPart c P' y ≠ ⊥ := by
    rw [highPart_of_le hy]
    exact fun h ↦ hc0 (le_bot_iff.mp (h ▸ hy))
  have h1 := one_le_valueRank_highPart hhy
  rw [highPart_of_le hy] at h1
  rw [glueRanks_of_lt hx, glueRanks_of_le hy]
  omega

/-- `min p r ≤ min q r` exactly when `p ≤ q` or `r ≤ q`. -/
theorem min_le_min_iff {β : Type*} [LinearOrder β] {p q r : β} :
    min p r ≤ min q r ↔ p ≤ q ∨ r ≤ q := by
  rw [le_min_iff, min_le_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, min_le_right _ _⟩⟩

include hℓF haH hP' in
/-- **The new ranks keep the order property of the old ranks and of the new values**: if the
old ranks and the new values both satisfy `min (· x) (· z) ≤ min (· y) (· z)`, so do the new
ranks.  If `y` is low, only the old ranks are used; if `y` is high, only the new values. -/
theorem min_glueRanks_le_min {x y z : ι} (hA : min (a x) (a z) ≤ min (a y) (a z))
    (hB : min (P' x) (P' z) ≤ min (P' y) (P' z)) :
    min (glueRanks a ℓ c P' x) (glueRanks a ℓ c P' z) ≤
      min (glueRanks a ℓ c P' y) (glueRanks a ℓ c P' z) := by
  have hl := lt_iff_lt hℓF haH hP'
  rw [min_le_min_iff] at hA hB ⊢
  by_cases hy : P' y < c
  · have hay := (hl y).mp hy
    rw [glueRanks_of_lt hy]
    rcases hA with h | h
    · have hx : P' x < c := (hl x).mpr (lt_of_le_of_lt h hay)
      exact .inl (by rwa [glueRanks_of_lt hx])
    · have hz : P' z < c := (hl z).mpr (lt_of_le_of_lt h hay)
      exact .inr (by rwa [glueRanks_of_lt hz])
  · have hcy : c ≤ P' y := not_lt.mp hy
    by_cases hx : P' x < c
    · exact .inl (glueRanks_lt_of_lt_of_le hℓF haH hP' hx hcy).le
    have hcx : c ≤ P' x := not_lt.mp hx
    rcases hB with h | h
    · exact .inl ((glueRanks_le_iff hcx hcy).mpr h)
    · by_cases hz : P' z < c
      · exact .inr (glueRanks_lt_of_lt_of_le hℓF haH hP' hz hcy).le
      · exact .inr ((glueRanks_le_iff (not_lt.mp hz) hcy).mpr h)

end Generic

/-! ### Lawful tables of the new ranks -/

/-- The strictly increasing positive table: `⊥` at `0`, the natural number `i` at `i > 0`. -/
noncomputable def natTable (i : ℕ) : Label.{u} := if i = 0 then ⊥ else (i : Label.{u})

theorem natTable_le_iff {i j : ℕ} : natTable.{u} i ≤ natTable j ↔ i ≤ j := by
  unfold natTable
  by_cases hi : i = 0
  · simp [hi]
  by_cases hj : j = 0
  · rw [ite_eq_right hi, ite_eq_left hj]
    simp only [le_bot_iff, hj, nonpos_iff_eq_zero, hi, iff_false]
    rw [natCast_label]
    exact WithBot.coe_ne_bot
  rw [ite_eq_right hi, ite_eq_right hj, natCast_label, natCast_label]
  constructor
  · intro h
    exact_mod_cast WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)
  · intro h
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast h))

theorem isPositiveTable_natTable (H : ℕ) : IsPositiveTable.{u} H natTable := by
  refine ⟨fun i j h ↦ natTable_le_iff.mpr h, by simp [natTable], fun i ↦ ?_, fun i hi _ ↦ ?_⟩
  · unfold natTable
    split_ifs with h
    · exact isSelfVisible_bot 1
    · exact (isSelfVisible_natCast i).mpr (Nat.one_le_iff_ne_zero.mpr h)
  · unfold natTable
    rw [ite_eq_right hi.ne', natCast_label]
    exact WithBot.coe_ne_bot

variable {n : ℕ} {S : Scheme.{u} n}

/-- The cells below a cell of grade one have grade one. -/
theorem grade_eq_one_of_mem_below (hwf : S.IsWellFormed) {s : Fin S.card}
    (hs : S.toCellScheme.grade s = 1)
    (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) : S.toCellScheme.grade d = 1 := by
  have h1 : S.toCellScheme.grade d ≤ 1 := hs ▸ d.2.2
  have h2 := hwf.isWellFormed.grade_pos d.1
  omega

/-- **The order property of ranks with lawful tables**, read off the strictly increasing table. -/
theorem min_le_min_of_hasLawfulTables (hwf : S.IsWellFormed) {H : ℕ} {w : Fin S.card → ℕ}
    (hw : Scheme.HasLawfulTables.{u} S H w) {s : Fin S.card} (hs : S.toCellScheme.grade s = 1)
    {d e : S.toCellScheme.below (S.toCellScheme.gradedIndex s)}
    (h : S.rows.row s e ≤ visibilityReplace 1 1 (S.rows.row s d)) :
    min (w e) (w s) ≤ min (w d) (w s) := by
  obtain ⟨hm, h0, hv, hp⟩ := isPositiveTable_natTable.{u} H
  have hZ := hw natTable hm h0 hv hp
  have h' := Scheme.min_le_min_of_isLawful hwf hZ hs h
  simp only [grade_eq_one_of_mem_below hwf hs, hs, ite_true] at h'
  rw [← hm.map_min, ← hm.map_min] at h'
  exact natTable_le_iff.mp h'

/-- **Availability of ranks with lawful tables**, read off the strictly increasing table. -/
theorem exists_le_of_hasLawfulTables {H : ℕ} {w : Fin S.card → ℕ}
    (hw : Scheme.HasLawfulTables.{u} S H w) {s t : Fin S.card} (hs : S.toCellScheme.grade s = 1)
    (ht : S.toCellScheme.grade t = 1) (hst : S.toCellScheme.scope s ⊆ S.toCellScheme.scope t) :
    ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex t ∧ w s ≤ w u := by
  obtain ⟨hm, h0, hv, hp⟩ := isPositiveTable_natTable.{u} H
  obtain ⟨u, hu, hle⟩ := (hw natTable hm h0 hv hp).availability s t hst (hs.trans ht.symm)
  have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
  simp only [hs, hgu, ite_true] at hle
  exact ⟨u, hu, natTable_le_iff.mp hle⟩

/-- A labelling lawful below `(univ, 1)`, extended by `⊥` above the grade one, is lawful. -/
theorem isLawful_of_isLawfulBelow_one (hwf : S.IsWellFormed) {v : Fin S.card → Label.{u}}
    (hv : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ v d) :
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then v d else ⊥ := by
  have hall (d : Fin S.card) : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), n) :=
    ⟨subset_univ _, (hwf.isWellFormed.grade_le_card d).trans
      ((card_le_univ _).trans_eq (Fintype.card_fin n))⟩
  have h := (CellScheme.Rows.isLawfulBelow_extendAbove (K := n) hv).isLawful hall
  convert h using 2 with d
  have := hwf.isWellFormed.grade_pos d
  by_cases h1 : S.toCellScheme.grade d = 1
  · simp [h1]
  · simp [h1, show ¬ S.toCellScheme.grade d ≤ 1 by omega]


/-- **The lawful-table argument.**  On a side whose old ranks have lawful tables and whose new
values are lawful below `(univ, 1)`, the new ranks have lawful tables: by order interpolation
(`Scheme.hasLawfulTables_of_order`) against the new values, with the order property of the old
ranks at the low fields and of the new values at the high ones
(`ProcessRank.min_glueRanks_le_min`). -/
theorem hasLawfulTables_glueRanks (hwf : S.IsWellFormed) {H ℓ : ℕ} {F : ℕ → Label.{u}}
    {c : Label.{u}} {a : Fin S.card ⊕ Fin S.card → ℕ} {P' : Fin S.card ⊕ Fin S.card → Label.{u}}
    (hℓF : ∀ i ≤ H, i < ℓ ↔ F i < c) (hF : IsPositiveTable H F) (haH : ∀ x, a x ≤ H)
    (hP' : ∀ x, min (P' x) c = min (F (a x)) c) (hrH : ∀ x, glueRanks a ℓ c P' x ≤ H)
    (b : Bool) (hab : Scheme.HasLawfulTables.{u} S H fun d ↦ a (sideField b d))
    (hv : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ P' (sideField b d)) :
    Scheme.HasLawfulTables.{u} S H fun d ↦ glueRanks a ℓ c P' (sideField b d) := by
  obtain ⟨-, hF0, -, hFpos⟩ := hF
  have hY := isLawful_of_isLawfulBelow_one hwf (v := fun d ↦ P' (sideField b d)) hv
  have hl := lt_iff_lt hℓF haH hP'
  refine Scheme.hasLawfulTables_of_order hwf (fun d _ ↦ hrH _) hY (fun d hd ↦ ?_)
    (fun s hs d e hde ↦ ?_) (fun s t hs ht hst ↦ ?_)
  · simp only [hd, ite_true]
    by_cases hx : P' (sideField b d) < c
    · rw [glueRanks_of_lt hx]
      have hax := (hl _).mp hx
      rw [eq_of_min_eq_of_lt (hP' _) ((hℓF _ (haH _)).mp hax)]
      constructor
      · intro h
        rw [h]
        exact hF0
      · intro h
        by_contra h0
        exact hFpos _ (Nat.pos_of_ne_zero h0) (haH _) h
    · have hcx := not_lt.mp hx
      rw [glueRanks_of_le hcx]
      have hrv : valueRank (highPart c P') (P' (sideField b d)) = 0 ↔ P' (sideField b d) = ⊥ := by
        rw [← highPart_of_le hcx]
        exact rankVector_eq_zero_iff (R := highPart c P') _
      constructor
      · intro h
        exact hrv.mp (by omega)
      · intro h
        have hl0 := (eq_bot_iff_eq_zero hℓF hF0).mp (le_bot_iff.mp (h ▸ hcx))
        rw [hl0, hrv.mpr h]
  · have hA := min_le_min_of_hasLawfulTables hwf hab hs hde
    have hB := Scheme.min_le_min_of_isLawful hwf hY hs hde
    simp only [grade_eq_one_of_mem_below hwf hs, hs, ite_true] at hB
    exact min_glueRanks_le_min hℓF haH hP' hA hB
  · by_cases hx : P' (sideField b s) < c
    · obtain ⟨u, hu, hle⟩ := exists_le_of_hasLawfulTables hab hs ht hst
      refine ⟨u, hu, ?_⟩
      by_cases hu' : P' (sideField b u) < c
      · rwa [glueRanks_of_lt hx, glueRanks_of_lt hu']
      · exact (glueRanks_lt_of_lt_of_le hℓF haH hP' hx (not_lt.mp hu')).le
    · obtain ⟨u, hu, hle⟩ := hY.availability s t hst (hs.trans ht.symm)
      have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
      simp only [hs, hgu, ite_true] at hle
      have hcu : c ≤ P' (sideField b u) := (not_lt.mp hx).trans hle
      exact ⟨u, hu, (glueRanks_le_iff (not_lt.mp hx) hcu).mpr hle⟩

/-! ### The restricted rank glue -/

/-- **The restricted rank glue.**  The prescribed side is the one-sided capped lift of the old
values `F ∘ a` with no admission (`ProcessRank.oneSidedStateLift` with no designated cells); the
other side is chosen on the RANKS: capped at `c` if `ℓ ≤ m(a)`; grafted with the high tail of
the prescribed side if `m(a) < ℓ`, `K ≤ 1` and `a` is separated; kept otherwise.  The new ranks
and table are `ProcessRank.glueRanks` and `ProcessRank.glueTable` of the new values. -/
theorem restrictedRankGlue : RestrictedRankGlueTarget.{u} := by
  intro n S hS T K H hTK hH hH0 b X hX hX1 a F c ℓ r ha hF hc hℓ hℓF hr hrF
  classical
  obtain ⟨haH, hadense, hatab, haadm⟩ := ha
  have hwf := hS.isWellFormed
  obtain ⟨hFm, hF0, hF1, hFpos⟩ := hF
  set P : Fin S.card ⊕ Fin S.card → Label.{u} := fun x ↦ F (a x) with hPdef
  have hPl : IsStateLawfulAt S 1 P := fun b' ↦ by
    have h := (hatab b' F hFm hF0 hF1 hFpos).isLawfulBelow ((univ : Finset (Fin n)), 1)
    refine (CellScheme.Rows.isLawfulBelow_congr
      (w := fun d ↦ if S.toCellScheme.grade d = 1 then F (a (sideField b' d)) else ⊥)
      (w' := fun d ↦ P (sideField b' d)) fun d hd ↦ ?_).mp h
    have h0 := hwf.isWellFormed.grade_pos d
    have h1 : S.toCellScheme.grade d = 1 := by
      have := hd.2
      change S.toCellScheme.grade d ≤ 1 at this
      omega
    simp [h1, hPdef]
  obtain ⟨P₀, hP₀l, hP₀1, -, hP₀r, hP₀c⟩ := oneSidedStateLift S hS ∅ 2 1
    (fun d hd ↦ absurd hd (Set.notMem_empty d)) b X hX ⟨subset_univ _, hX1.le⟩ c P r hc hPl
    (fun _ ↦ hF1 _) (isAdmitted_of_lt (by decide)) hr hrF
  set R : Fin S.card → Label.{u} := fun d ↦ P₀ (sideField b d) with hRdef
  set PO : Fin S.card → Label.{u} := fun d ↦ P (sideField (!b) d) with hPOdef
  have hRl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d := hP₀l b
  have hRc (d : Fin S.card) : min (R d) c = min (P (sideField b d)) c := hP₀c _
  have hPOl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ PO d := hPl (!b)
  have hcard : Fintype.card (Fin S.card ⊕ Fin S.card) ≤ H := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  -- the capped agreement of a new state with the old values
  have hcapO (O : Fin S.card → Label.{u}) (hOc : ∀ d, min (O d) c = min (PO d) c) :
      ∀ x, min (stateOf b R O x) c = min (F (a x)) c :=
    (forall_field_iff b).mpr fun d ↦ by
      simp only [stateOf_sideField_self, stateOf_sideField_not]
      exact ⟨hRc d, hOc d⟩
  -- the conclusion from a choice of the other side
  have hfinish (O : Fin S.card → Label.{u})
      (hOl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ O d)
      (hO1 : ∀ d, IsSelfVisible 1 (O d)) (hOc : ∀ d, min (O d) c = min (PO d) c)
      (hA : IsAdmitted T K 1 (glueRanks a ℓ c (stateOf b R O))) :
      ∃ (a' : Fin S.card ⊕ Fin S.card → ℕ) (F' : ℕ → Label.{u}),
        IsSpanRankMember S H T K a' ∧ IsPositiveTable H F' ∧ (∀ x, min (a x) ℓ = min (a' x) ℓ) ∧
        (∀ i < ℓ, F' i = F i) ∧ (∀ i ≤ H, min (F' i) c = min (F i) c) ∧
        (∀ x, min (F' (a' x)) c = min (F (a x)) c) ∧
        ∀ d : S.toCellScheme.below X, F' (a' (sideField b d.1)) = r d := by
    set P' := stateOf b R O with hP'def
    have hP'c := hcapO O hOc
    have hP'1 : ∀ x, IsSelfVisible 1 (P' x) := (forall_field_iff b).mpr fun d ↦ by
      simp only [hP'def, stateOf_sideField_self, stateOf_sideField_not]
      exact ⟨hP₀1 _, hO1 d⟩
    have hP'l (b' : Bool) :
        S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ P' (sideField b' d) := by
      rcases Bool.eq_or_eq_not b' b with rfl | rfl
      · simpa [hP'def] using hRl
      · simpa [hP'def] using hOl
    have hrH := glueRanks_le hℓF haH hP'c hcard hadense
    refine ⟨glueRanks a ℓ c P', glueTable F ℓ c P',
      ⟨hrH, glueRanks_dense hℓF haH hP'c hadense, fun b' ↦ hasLawfulTables_glueRanks hwf hℓF
        ⟨hFm, hF0, hF1, hFpos⟩ haH hP'c hrH b' (hatab b') (hP'l b'), hA⟩,
      isPositiveTable_glueTable hℓF hF0 ⟨hFm, hF0, hF1, hFpos⟩ hP'1 hℓ,
      min_glueRanks hℓF hF0 haH hP'c, fun i hi ↦ glueTable_of_lt hi,
      fun i hi ↦ min_glueTable hℓF hF0 hi, fun x ↦ ?_, fun d ↦ ?_⟩
    · rw [glueTable_glueRanks hℓF hF0 haH hP'c]
      exact hP'c x
    · rw [glueTable_glueRanks hℓF hF0 haH hP'c, stateOf_sideField_self]
      exact hP₀r d
  -- the choice of the other side, on the ranks
  by_cases hKk : K ≤ 1
  swap
  · exact hfinish PO hPOl (fun _ ↦ hF1 _) (fun _ ↦ rfl) fun hK ↦ absurd hK hKk
  have hdes {d : Fin S.card} (hd : d ∈ T) (b' : Bool) : IsDesignated T (sideField b' d) := by
    cases b' <;> exact hd
  have hundes {d : Fin S.card} (hd : d ∉ T) (b' : Bool) : ¬ IsDesignated T (sideField b' d) := by
    cases b' <;> exact hd
  by_cases h1 : ℓ ≤ undesignatedMax T a
  · -- case 1: cap the other side at `c`
    refine hfinish (fun d ↦ min (PO d) c) (hPOl.min_const_of_isSelfVisible hc)
      (fun d ↦ (hF1 _).min hc) (fun d ↦ by rw [min_assoc, min_self]) ?_
    rintro - hsep d hd
    exfalso
    set P' := stateOf b R fun d ↦ min (PO d) c with hP'def
    have hP'c := hcapO (fun d ↦ min (PO d) c) fun d ↦ by rw [min_assoc, min_self]
    obtain ⟨hpos, hlt⟩ := hsep _ (hdes hd (!b))
    have hle : P' (sideField (!b) d) ≤ c := by
      rw [hP'def, stateOf_sideField_not]
      exact min_le_right _ _
    by_cases hc0 : c = ⊥
    · have hl0 : ℓ = 0 := (eq_bot_iff_eq_zero hℓF hF0).mp hc0
      have hP0 : P' (sideField (!b) d) = ⊥ := le_bot_iff.mp (hc0 ▸ hle)
      have hcx : c ≤ P' (sideField (!b) d) := hc0 ▸ bot_le
      rw [glueRanks_of_le hcx, hP0, valueRank_bot, hl0] at hpos
      exact absurd hpos (lt_irrefl _)
    · have hl1 : 1 ≤ ℓ :=
        Nat.one_le_iff_ne_zero.mpr fun h ↦ hc0 ((eq_bot_iff_eq_zero hℓF hF0).mpr h)
      have hne : (univ.filter fun x ↦ ¬ IsDesignated T x).Nonempty := by
        by_contra hem
        rw [not_nonempty_iff_eq_empty] at hem
        have : undesignatedMax T a = 0 := by
          unfold undesignatedMax
          rw [hem, sup_empty]
          rfl
        omega
      obtain ⟨e, he, hem⟩ := exists_mem_eq_sup _ hne a
      have hae : ℓ ≤ a e := h1.trans_eq (by unfold undesignatedMax; exact hem)
      have hce : c ≤ P' e := not_lt.mp fun h ↦ (not_lt.mpr hae) ((lt_iff_lt hℓF haH hP'c e).mp h)
      have hge : glueRanks a ℓ c P' (sideField (!b) d) ≤ glueRanks a ℓ c P' e := by
        by_cases ht : P' (sideField (!b) d) < c
        · exact (glueRanks_lt_of_lt_of_le hℓF haH hP'c ht hce).le
        · exact (glueRanks_le_iff (not_lt.mp ht) hce).mpr
            ((le_antisymm hle (not_lt.mp ht)).trans_le hce)
      exact absurd (hlt e (mem_filter.mp he).2) (not_lt.mpr hge)
  rw [not_le] at h1
  have hlowU {y : Fin S.card ⊕ Fin S.card} (hy : ¬ IsDesignated T y) : a y < ℓ :=
    (le_undesignatedMax hy).trans_lt h1
  by_cases hsepa : IsSeparated T a
  · -- case 3: graft the high tail of the prescribed side onto the other side
    have hBO (d : Fin S.card) (hd : d ∈ T) : a (sideField b d) = a (sideField (!b) d) := by
      have := haadm hKk hsepa d hd
      rwa [inl_eq_inr_iff_sideField b] at this
    have hRB (d : Fin S.card) : c ≤ R d ↔ c ≤ P (sideField b d) := by
      rw [← min_eq_right_iff, ← min_eq_right_iff (a := P (sideField b d)), hRc d]
    have hhigh (d : Fin S.card) : c ≤ PO d ↔ c ≤ R d := by
      rw [hRB]
      by_cases hd : d ∈ T
      · simp only [hPOdef, hPdef, hBO d hd]
      · have h₁ := (hℓF _ (haH _)).mp (hlowU (hundes hd b))
        have h₂ := (hℓF _ (haH _)).mp (hlowU (hundes hd (!b)))
        exact iff_of_false (not_le.mpr h₂) (not_le.mpr h₁)
    refine hfinish (fun d ↦ if c ≤ PO d then R d else PO d)
      (Scheme.graftHighTail S _ PO R c hPOl hRl hc
        fun d _ ↦ hhigh d)
      (fun d ↦ by split_ifs; exacts [hP₀1 _, hF1 _]) (fun d ↦ ?_) ?_
    · split_ifs with h
      · rw [min_eq_right h, min_eq_right ((hhigh d).mp h)]
      · rfl
    · rintro - - d hd
      set O := fun d ↦ if c ≤ PO d then R d else PO d with hOdef
      have hP'c := hcapO O fun d ↦ by
        rw [hOdef]
        beta_reduce
        split_ifs with h
        · rw [min_eq_right h, min_eq_right ((hhigh d).mp h)]
        · rfl
      rw [inl_eq_inr_iff_sideField b]
      by_cases hcd : c ≤ PO d
      · have hx : c ≤ stateOf b R O (sideField b d) := by
          rw [stateOf_sideField_self]
          exact (hhigh d).mp hcd
        have hy : c ≤ stateOf b R O (sideField (!b) d) := by
          rw [stateOf_sideField_not, hOdef]
          simp only [hcd, ite_true]
          exact (hhigh d).mp hcd
        rw [glueRanks_of_le hx, glueRanks_of_le hy, stateOf_sideField_self,
          stateOf_sideField_not, hOdef]
        simp only [hcd, ite_true]
      · have hlo : a (sideField (!b) d) < ℓ := (hℓF _ (haH _)).mpr (not_le.mp hcd)
        have hx := (lt_iff_lt hℓF haH hP'c (sideField b d)).mpr (hBO d hd ▸ hlo)
        have hy := (lt_iff_lt hℓF haH hP'c (sideField (!b) d)).mpr hlo
        rw [glueRanks_of_lt hx, glueRanks_of_lt hy]
        exact hBO d hd
  · -- case 2: keep the other side; the new ranks stay inactive
    refine hfinish PO hPOl (fun _ ↦ hF1 _) (fun _ ↦ rfl) fun _ hsep ↦ absurd ?_ hsepa
    have hP'c := hcapO PO fun _ ↦ rfl
    have hl1 : 1 ≤ ℓ := lt_of_le_of_lt (Nat.zero_le _) h1
    intro x hx
    obtain ⟨hpos, hlt⟩ := hsep x hx
    have hlowg {y : Fin S.card ⊕ Fin S.card} (hy : ¬ IsDesignated T y) :
        glueRanks a ℓ c (stateOf b R PO) y = a y :=
      glueRanks_of_lt ((lt_iff_lt hℓF haH hP'c y).mpr (hlowU hy))
    by_cases hxl : stateOf b R PO x < c
    · rw [glueRanks_of_lt hxl] at hpos hlt
      exact ⟨hpos, fun y hy ↦ (hlowg hy) ▸ hlt y hy⟩
    · have hax : ℓ ≤ a x := not_lt.mp fun h ↦ hxl ((lt_iff_lt hℓF haH hP'c x).mpr h)
      exact ⟨lt_of_lt_of_le hl1 hax, fun y hy ↦ (hlowU hy).trans_le hax⟩

end VaughtConjecture.ProcessRank

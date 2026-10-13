/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Structure

/-!
# The decoder round trip (target B.T5)

Numbering as in the current draft of [AFK26].

**Compatible structures** (correspondence with the printed definitions).  In a structure
compatible with `ID[L]` ([AFK26, Definitions 2.5 and 4.18]):

* a tuple with an invariant `Q_c` has, along every sequence of places, exactly the relations
  that `c` prescribes (`IsTemplateCompatible.relMap_comp_iff`, the pairs);
* it is injective (`IsTemplateCompatible.injective_of_relMap_invariant`, clauses (a) and (b) of
  [AFK26, Definition 2.2]) and has one invariant (`IsTemplateCompatible.eq_of_relMap_invariant`,
  clause (c));
* every tuple on `k ≥ 1` places is a sequence of places of a tuple with an invariant
  (`IsTemplateCompatible.exists_relMap_invariant_comp`, the second clause of
  [AFK26, Definition 2.1]: its points extend to a closed tuple);
* if the structure is fixed by `τ_β`, every invariant it realizes is fixed by `τ_β`
  (`IsTemplateCompatible.project_eq_of_relMap_invariant`).

**The decoder** (native construction).  For a compatible structure, a tuple on `n ≥ 1` points
decodes to `c` reduced to `ω + ω · β` exactly when `Q_c` holds of it
(`decode_eval_eq_some_iff`, `decode_eval_eq_none_iff`); the decoded class realization is well
formed, at every `β` and without fixedness (`IsTemplateCompatible.isWellFormed_decode`); for a
structure fixed by `τ_β`, at every `β`, its structure is the given one, every symbol included
(`IsTemplateCompatible.toStructure_decode`).

**Target B.T5** (`decoderRoundTrip`): for `β < ω₁`, `DecoderRoundTrip β M`, with the premises
`IsTemplateCompatible G` and `projectStructure β G = G` in the first half and
`R.IsWellFormed` in the second.  The first half holds at every `β`; `β < ω₁` is used in the
second (`ClassRealization.projectStructure_toStructure`, `decode_toStructure`).  The proof uses
the two clauses of [AFK26, Definition 2.5] only (not the third clause of [AFK26, Definition
2.4]), and no positional presentation of class data.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

variable {M : Type v} {G : templateLanguage.{u}.Structure M} {β : Ordinal.{u}}

/-! ### Compatible structures -/

namespace IsTemplateCompatible

variable (hG : IsTemplateCompatible G)
include hG

/-- **The pairs of `ID[L]`, in a compatible structure.**  Correspondence with the printed
definitions. -/
theorem relMap_comp_iff {n k : ℕ} {hn : 0 < n} {c : LegalClass.{u} n} {x : Fin n → M}
    (hx : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x)
    (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) :
    RelMap (L := templateLanguage.{u}) r (x ∘ i) ↔ c.1.Holds r i :=
  (satisfiesPairs_templateDiagramPairs_iff G).mp hG.2 hn c x hx r i

/-- **A tuple with an invariant is injective** ([AFK26, Definitions 2.1 and 2.2 (b)]).
Correspondence with the printed definitions. -/
theorem injective_of_relMap_invariant {n : ℕ} {hn : 0 < n} {c : LegalClass.{u} n}
    {x : Fin n → M} (hx : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x) :
    Function.Injective x :=
  hG.1.isGeometry.injective hn x ((hG.1.closed_iff hn x).mpr
    ⟨TemplateSymbol.invariant c hn, trivial, hx⟩)

/-- **A tuple has at most one invariant** ([AFK26, Definition 2.2 (c)]).  Correspondence with the
printed definitions. -/
theorem eq_of_relMap_invariant {n : ℕ} {hn : 0 < n} {c d : LegalClass.{u} n} {x : Fin n → M}
    (hc : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x)
    (hd : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant d hn) x) : c = d := by
  by_contra h
  exact hG.1.exclusive (TemplateSymbol.invariant c hn) (TemplateSymbol.invariant d hn) trivial
    trivial (fun h' ↦ h (by injection h')) x hc hd

/-- **Every tuple is a sequence of places of a tuple with an invariant** ([AFK26,
Definitions 2.1 and 2.2 (b)]).  Correspondence with the printed definitions. -/
theorem exists_relMap_invariant_comp {k : ℕ} (hk : 0 < k) (xs : Fin k → M) :
    ∃ (n : ℕ) (hn : 0 < n) (c : LegalClass.{u} n) (y : Fin n → M) (i : Fin k → Fin n),
      RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) y ∧ xs = y ∘ i := by
  classical
  let s : Finset M := Finset.univ.image xs
  have hmem (a : Fin k) : xs a ∈ s := Finset.mem_image_of_mem xs (Finset.mem_univ a)
  have hs : 0 < s.card := Finset.card_pos.mpr ⟨_, hmem ⟨0, hk⟩⟩
  let w : Fin s.card → M := fun j ↦ (s.equivFin.symm j : M)
  have hw : Function.Injective w := fun a b hab ↦ s.equivFin.symm.injective (Subtype.ext hab)
  obtain ⟨l, y, hyw, hy⟩ := hG.1.isGeometry.exists_closed hs w hw
  obtain ⟨Q, hQ, hQy⟩ := (hG.1.closed_iff _ y).mp hy
  rcases Q with _ | ⟨c, hn⟩ | _ <;> try exact hQ.elim
  refine ⟨_, hn, c, y, fun a ↦ Fin.castAdd l (s.equivFin ⟨xs a, hmem a⟩), hQy, funext fun a ↦ ?_⟩
  have := congrFun hyw (s.equivFin ⟨xs a, hmem a⟩)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, w] at this
  exact this.symm

/-- **In a structure fixed by `τ_β`, every realized invariant is fixed by `τ_β`.**
Correspondence with the printed definitions. -/
theorem project_eq_of_relMap_invariant (hfix : projectStructure β G = G) {n : ℕ} {hn : 0 < n}
    {c : LegalClass.{u} n} {x : Fin n → M}
    (hx : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x) :
    c.project β = c := by
  have h : RelMap (L := templateLanguage.{u}) (self := projectStructure β G)
      (TemplateSymbol.invariant (c.project β) hn) x := ⟨c, rfl, hx⟩
  rw [hfix] at h
  exact (hG.eq_of_relMap_invariant hx h).symm

end IsTemplateCompatible

/-- A legal class fixed by `τ_β`, reduced to `ω + ω · β`, has itself as its class at `ω₁`.
Native construction. -/
theorem LegalClass.globalClass_reduce_of_project_eq {n : ℕ} {c : LegalClass.{u} n}
    (hc : c.project β = c) : (c.1.reduce (isSuccPrelimit_blockStage β)).globalClass = c.1 := by
  have := congrArg Subtype.val hc
  rw [LegalClass.coe_project, TemplateClass.project_eq_reduce_reduce] at this
  exact this

/-! ### The decoder on compatible structures -/

open Classical in
/-- The decoder on a tuple on `n + 1` points.  Native construction. -/
theorem decode_eval_succ (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) {n : ℕ}
    (t : Fin (n + 1) ↪ M) :
    (decode β G).eval t = if h : ∃ c : LegalClass.{u} (n + 1),
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c n.succ_pos) t
      then some (h.choose.1.reduce (isSuccPrelimit_blockStage β)) else none :=
  rfl

/-- The decoder on the empty tuple.  Native construction. -/
@[simp] theorem decode_eval_zero (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M)
    (t : Fin 0 ↪ M) : (decode β G).eval t = some (TemplateClass.empty _) :=
  rfl

/-- **A tuple on `n ≥ 1` points decodes to `e` exactly when `e` is the reduction to `ω + ω · β`
of an invariant of the tuple**, in a compatible structure.  Native construction. -/
theorem decode_eval_eq_some_iff (hG : IsTemplateCompatible G) {n : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) (e : TemplateClass.{u} (blockStage β) n) :
    (decode β G).eval t = some e ↔ ∃ c : LegalClass.{u} n,
      RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) t ∧
        c.1.reduce (isSuccPrelimit_blockStage β) = e := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [decode_eval_succ]
  split_ifs with h
  · constructor
    · intro he
      exact ⟨h.choose, h.choose_spec, Option.some.inj he⟩
    · rintro ⟨c, hc, rfl⟩
      rw [hG.eq_of_relMap_invariant h.choose_spec hc]
  · refine ⟨fun he ↦ absurd he (by simp), ?_⟩
    rintro ⟨c, hc, -⟩
    exact absurd ⟨c, hc⟩ h

/-- **A tuple on `n ≥ 1` points is undecoded exactly when it has no invariant.**  Native
construction. -/
theorem decode_eval_eq_none_iff (hG : IsTemplateCompatible G) {n : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) :
    (decode β G).eval t = none ↔ ∀ c : LegalClass.{u} n,
      ¬ RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) t := by
  constructor
  · intro h c hc
    have := (decode_eval_eq_some_iff (β := β) hG hn t _).mpr ⟨c, hc, rfl⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    cases he : (decode β G).eval t with
    | none => rfl
    | some e =>
      obtain ⟨c, hc, -⟩ := (decode_eval_eq_some_iff hG hn t e).mp he
      exact absurd hc (h c)

namespace IsTemplateCompatible

variable (hG : IsTemplateCompatible G)
include hG

/-- **The decoder of a compatible structure is consistent.**  Native construction. -/
theorem isConsistent_decode : (decode β G).IsConsistent := by
  intro m n t e f he
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [decode_eval_zero, TemplateClass.restrictFace_zero]
  have hn : 0 < n := hm.trans_le (by simpa using Fintype.card_le_of_embedding f)
  obtain ⟨c, hc, rfl⟩ := (decode_eval_eq_some_iff hG hn t e).mp he
  rw [TemplateClass.restrictFace_reduce]
  cases hs : c.1.restrictFace f with
  | none =>
    refine (decode_eval_eq_none_iff hG hm _).mpr fun d hd ↦ ?_
    obtain ⟨_, s, hs', -⟩ := (hG.relMap_comp_iff hc (TemplateSymbol.invariant d hm) f).mp hd
    have hs'' : c.1.restrictFace f = some s := hs'
    rw [hs] at hs''
    exact absurd hs'' (by simp)
  | some s =>
    have hsl : s.IsStronglyCodedLegal := c.2.restrictFace hs
    refine (decode_eval_eq_some_iff hG hm _ _).mpr ⟨⟨s, hsl⟩, ?_, rfl⟩
    exact (hG.relMap_comp_iff hc (TemplateSymbol.invariant ⟨s, hsl⟩ hm) f).mpr
      ⟨f.injective, s, hs, rfl⟩

/-- **The decoder of a compatible structure is covering.**  Native construction. -/
theorem isCovering_decode : (decode β G).IsCovering := by
  intro n t
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, t, Function.Embedding.refl _, rfl, by simp⟩
  obtain ⟨k, y, hyt, hy⟩ := hG.1.isGeometry.exists_closed hn t t.injective
  obtain ⟨Q, hQ, hQy⟩ := (hG.1.closed_iff _ y).mp hy
  rcases Q with _ | ⟨c, hn'⟩ | _ <;> try exact hQ.elim
  have hyi := hG.injective_of_relMap_invariant hQy
  refine ⟨n + k, ⟨y, hyi⟩, Fin.castAddEmb k, Function.Embedding.ext fun i ↦ ?_, ?_⟩
  · exact congrFun hyt i
  · rw [Option.isSome_iff_exists]
    exact ⟨_, (decode_eval_eq_some_iff hG hn' ⟨y, hyi⟩ _).mpr ⟨c, hQy, rfl⟩⟩

/-- **The decoder of a compatible structure has legal types.**  Native construction. -/
theorem hasLegalTypes_decode : (decode β G).HasLegalTypes := by
  intro n t e he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [TemplateClass.eq_empty e]
    exact ⟨(Correspondence.isLegal_intervalScheme 0).isLegal_toStageType _,
      fun _ _ ↦ Label.isStronglyCoded_bot _⟩
  obtain ⟨c, -, rfl⟩ := (decode_eval_eq_some_iff hG hn t e).mp he
  exact (TemplateClass.isStronglyCodedLegal_reduce_iff _ _).mpr c.2

/-- **The decoder of a compatible structure is well formed**, at every `β`, without
fixedness.  Native construction. -/
theorem isWellFormed_decode : (decode β G).IsWellFormed :=
  ⟨hG.isConsistent_decode, hG.isCovering_decode, hG.hasLegalTypes_decode⟩

/-- **The structure of the decoder of a compatible structure fixed by `τ_β` is the structure**:
every symbol holds of the same tuples.  Native construction. -/
theorem toStructure_decode (hfix : projectStructure β G = G) :
    (decode β G).toStructure = G := by
  refine templateStructure_ext fun r xs ↦ ?_
  have hk := TemplateSymbol.pos r
  constructor
  · rintro ⟨h, e, he, hr⟩
    obtain ⟨c, hc, rfl⟩ := (decode_eval_eq_some_iff hG hk ⟨xs, h⟩ e).mp he
    rw [LegalClass.globalClass_reduce_of_project_eq
      (hG.project_eq_of_relMap_invariant hfix hc)] at hr
    have := (hG.relMap_comp_iff hc r id).mpr
      ⟨Function.injective_id, c.1, TemplateClass.restrictFace_refl c.1, hr⟩
    exact this
  · intro hr
    obtain ⟨n, hn, c, y, i, hy, rfl⟩ := hG.exists_relMap_invariant_comp hk xs
    obtain ⟨hi, s, hs, hrs⟩ := (hG.relMap_comp_iff hy r i).mp hr
    have hsl : s.IsStronglyCodedLegal := c.2.restrictFace hs
    have hsy : RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant ⟨s, hsl⟩ hk) (y ∘ i) :=
      (hG.relMap_comp_iff hy _ i).mpr ⟨hi, s, hs, rfl⟩
    have hinj := hG.injective_of_relMap_invariant hsy
    refine ⟨hinj, _,
      (decode_eval_eq_some_iff hG hk ⟨y ∘ i, hinj⟩ _).mpr ⟨⟨s, hsl⟩, hsy, rfl⟩, ?_⟩
    rw [LegalClass.globalClass_reduce_of_project_eq
      (hG.project_eq_of_relMap_invariant hfix hsy)]
    exact hrs

end IsTemplateCompatible

/-- **Target B.T5, the decoder round trip** ([AFK26, Definitions 2.5, 2.7, 4.16 and 4.18]), for
`β < ω₁`: compatible `β`-fixed structures and well-formed class realizations at `ω + ω · β`
correspond, every symbol preserved.  Correspondence with the printed definitions. -/
theorem decoderRoundTrip (hβ : β < ω₁) : DecoderRoundTrip β M :=
  ⟨fun _ hG hfix ↦ ⟨hG.isWellFormed_decode, hG.toStructure_decode hfix⟩,
    fun R hR ↦ ⟨hR.isTemplateCompatible, ClassRealization.projectStructure_toStructure hβ R,
      decode_toStructure hβ hR⟩⟩

end

end VaughtConjecture

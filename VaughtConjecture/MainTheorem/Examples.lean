/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Assembly
import VaughtConjecture.MainTheorem.CapToModel

/-!
# Examples of the conditional composition

The hypotheses of `VaughtConjecture.MainTheorem.Assembly` on abstract types of classes (the
countable ordinals, with or without `2 ^ ℵ₁` further classes, and a single class), with the
observations "is the class `s`", which separate distinct classes, and, for the full-presentation
route, the structures `M S` on `ℕ` in a language of unary relations.

* The **tail domains** of the countable ordinals (stage `ξ` keeps the ordinals `≥ ξ`, so every
  stage at or above `ω₁` is empty) satisfy every hypothesis, and the composition gives exactly
  `ℵ₁` classes; the persistent core is empty.
* **Logical agreement is needed**: adjoining `2 ^ ℵ₁` further classes lying in every domain below
  `ω₁` keeps the domain laws, countable losses, and nonempty losses, but gives more than `ℵ₁`
  classes; so no family of observations separating the classes is constant on the domains.
* **Countable losses are needed**: adjoining `2 ^ ℵ₁` further classes all lost at the first
  successor keeps the domain laws, nonempty losses, and logical agreement, but gives more than
  `ℵ₁` classes.
* **Nonempty losses are needed**: a single class in every domain below `ω₁` satisfies the domain
  laws, countable losses, and logical agreement, and there are fewer than `ℵ₁` classes.

The tail domains repeat the private tail filtration of `VaughtConjecture.Counting.Separation`,
as expansion domains; that example is private to its file.

For the full-presentation route:

* The tail domains are the **filtration by a rank** (`Counting.Filtration.ofRank`), the rank of a
  countable ordinal being the ordinal itself, and the filtration of the expansion domains above;
  they are also the least-level filtration of the countable ordinals each presented at its own
  level.  The persistent core is empty.  These full presentations have bounded comparison for the
  truth predicate "the class is below the quantifier rank of the sentence", which holds at no
  class of the tail at the quantifier rank: both hypotheses hold together on `ℵ₁` classes.
* **Noncollapse is needed**: a single class, presented at level `0`, has full presentations at
  countable levels and bounded comparison for every truth predicate, and there is one class.
* **A prescribed age is needed** for the countability of the classes presented at a level: in the
  language of the unary relations `P n` (`n : ℕ`), the structure `M S` on `ℕ` interpreting `P n`
  as everything for `n ∈ S` and as nothing otherwise has every permutation as an automorphism,
  and the `2 ^ ℵ₀` structures `M S` are pairwise nonisomorphic.  So a level cannot present only
  countably many classes through an extension property alone (every permutation of `ℕ` is an
  automorphism of each `M S`, so each `M S` has the extension property for its own age, and
  distinct `S` give distinct ages); the age of the full structure has to be prescribed.
* **Countably many back-and-forth classes are needed** for thinness in scatteredness form
  (`isThinOn_of_countable_bfClasses`): the codes on `ℕ` of the structures `M S` depend
  continuously on `S`, as a point of Cantor space, and are pairwise nonisomorphic, so they form a
  nonempty perfect set of pairwise nonisomorphic codes (the library's
  `HasCantorAntichainOn.hasPerfectAntichainOn`).  By `isThinOn_of_countable_bfClasses`, the codes
  of this language fall into uncountably many classes of back-and-forth equivalence at some level
  `η < ω₁`.  The level is not computed here: `1` suffices (a point of `M S` and a point of `M T`
  have the same atomic type only if `S = T`), while `0` does not (the empty tuples satisfy no
  atomic formula).

For the hypothesis `CapToModel`: under the coatom extension property with apex at `ω`
(`CapToModel.of_hasApexCoatomExtensions`), the models of the density sentence on the carriers of
`Type 1` are infinite.
-/

namespace VaughtConjecture.MainTheorem

open Cardinal Set FirstOrder Counting
open scoped Ordinal

section Examples

/-- The countable ordinals. -/
private abbrev CountableOrdinal : Type 1 := Iio (ω₁ : Ordinal.{0})

/-- The `2 ^ ℵ₁` further classes: the sets of countable ordinals. -/
private abbrev FurtherClasses : Type 1 := Set CountableOrdinal

/-- There are exactly `ℵ₁` countable ordinals. -/
private theorem mk_countableOrdinal : #CountableOrdinal = ℵ₁ := by
  simp [mk_Iio_ordinal]

/-- Adjoining the further classes gives more than `ℵ₁` classes. -/
private theorem aleph_one_lt_mk_sum : ℵ₁ < #(CountableOrdinal ⊕ FurtherClasses) :=
  calc ℵ₁ < 2 ^ ℵ₁ := cantor _
    _ = #FurtherClasses := by rw [mk_set, mk_countableOrdinal]
    _ ≤ _ := mk_le_of_injective Sum.inr_injective

/-- The observations "is the class `s`" separate distinct classes. -/
private theorem separates_eq {X : Type*} (p q : X) (h : p ≠ q) :
    ∃ s : X, ¬ ((p = s) ↔ (q = s)) :=
  ⟨p, by simp [Ne.symm h]⟩

/-- The class `s` is not in a domain that excludes it, so "is the class `s`" is constant there. -/
private theorem uniform_eq {X : Type*} {D : Set X} {s : X} (hs : s ∉ D) :
    ∀ p ∈ D, ∀ q ∈ D, ((p = s) ↔ (q = s)) := by
  intro p hp q hq
  have hp' : p ≠ s := by rintro rfl; exact hs hp
  have hq' : q ≠ s := by rintro rfl; exact hs hq
  simp only [hp', hq']

/-- The successor of a countable ordinal is countable. -/
private theorem add_one_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) : ξ + 1 < ω₁ :=
  (isSuccLimit_omega 1).succ_lt hξ

/-- One is a countable ordinal. -/
private theorem one_lt_omega_one : (1 : Ordinal.{0}) < ω₁ :=
  Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one

/-- A countable ordinal is not at least its successor. -/
private theorem not_add_one_le (ξ : Ordinal.{0}) : ¬ ξ + 1 ≤ ξ :=
  (Order.lt_add_one_iff.2 le_rfl).not_ge

/-! ### The tail domains -/

/-- The tail domains of the countable ordinals: stage `ξ` keeps the ordinals `≥ ξ`, so the
stages at or above `ω₁` are empty. -/
private def tail : ExpansionDomains CountableOrdinal where
  domain ξ := {x | ξ ≤ x.1}
  zero := eq_univ_of_forall fun x ↦ (zero_le : (0 : Ordinal) ≤ x.1)
  antitone _ _ h _ hx := h.trans hx
  limit l hl _ x hx := by
    by_contra h
    exact not_add_one_le x.1 (mem_iInter₂.1 hx _ (hl.succ_lt (not_le.1 h)))
  domain_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun x hx ↦ (h.trans hx).not_gt x.2

/-- A class in the loss of the tail domains at `ξ` is the ordinal `ξ`. -/
private theorem eq_of_mem_tail_loss {ξ : Ordinal.{0}} {x : CountableOrdinal}
    (hx : x ∈ tail.domain ξ \ tail.domain (ξ + 1)) : x.1 = ξ :=
  (Order.lt_add_one_iff.1 (not_le.1 hx.2)).antisymm hx.1

/-- The tail domains have countable losses: each loss is at most one ordinal. -/
private theorem tail_hasCountableLosses : tail.HasCountableLosses :=
  ⟨fun _ _ ↦ Subsingleton.countable fun _ ha _ hb ↦
    Subtype.ext ((eq_of_mem_tail_loss ha).trans (eq_of_mem_tail_loss hb).symm)⟩

/-- The tail domains have nonempty losses: the loss at `ξ` contains `ξ`. -/
private theorem tail_hasNonemptyLosses : tail.HasNonemptyLosses :=
  ⟨fun ξ hξ ↦ ⟨⟨ξ, hξ⟩, le_refl ξ, not_add_one_le ξ⟩⟩

/-- The class `s` is not in the tail domain just above it. -/
private theorem notMem_tail_domain_add_one (s : CountableOrdinal) : s ∉ tail.domain (s.1 + 1) :=
  not_add_one_le s.1

/-- The tail domains have logical agreement for the observations "is the class `s`": each is false
on the domain just above `s`. -/
private theorem tail_hasLogicalAgreement :
    tail.HasLogicalAgreement fun (s x : CountableOrdinal) ↦ x = s :=
  ⟨fun s ↦ ⟨s.1 + 1, add_one_lt_omega_one s.2, uniform_eq (notMem_tail_domain_add_one s)⟩⟩

/-- **The composition applies to the tail domains**: exactly `ℵ₁` classes, from the four
hypotheses and separation. -/
example : #CountableOrdinal = ℵ₁ :=
  tail.mk_eq_aleph_one tail_hasCountableLosses tail_hasNonemptyLosses tail_hasLogicalAgreement
    separates_eq

/-- The persistent core of the tail domains is empty. -/
example : (⋂ ξ < ω₁, tail.domain ξ) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦
    notMem_tail_domain_add_one x (mem_iInter₂.1 hx _ (add_one_lt_omega_one x.2))

/-! ### Logical agreement is needed -/

/-- The tail domains with the further classes adjoined to every domain below `ω₁`. -/
private def adjoinPersistent : ExpansionDomains (CountableOrdinal ⊕ FurtherClasses) where
  domain ξ := {z | Sum.elim (· ∈ tail.domain ξ) (fun _ ↦ ξ < ω₁) z}
  zero := eq_univ_of_forall fun
    | .inl x => by simp [tail.zero]
    | .inr _ => Ordinal.omega_pos 1
  antitone _ _ h
    | .inl _, hx => tail.antitone h hx
    | .inr _, hx => h.trans_lt hx
  limit l hl hlt
    | .inl x, hx => tail.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ mem_iInter₂.1 hx ξ hξ)
    | .inr _, _ => hlt
  domain_eq_empty_of_omega_one_le ξ h := eq_empty_of_forall_notMem fun
    | .inl x, hx => by simp [tail.domain_eq_empty_of_omega_one_le ξ h] at hx
    | .inr _, hx => h.not_gt hx

/-- **Logical agreement cannot be dropped**: the domains with the further classes adjoined have
countable and nonempty losses and more than `ℵ₁` classes, so no family of observations
separating the classes is constant on the domains. -/
example : adjoinPersistent.HasCountableLosses ∧ adjoinPersistent.HasNonemptyLosses ∧
    ℵ₁ < #(CountableOrdinal ⊕ FurtherClasses) ∧
    ∀ (truth : CountableOrdinal ⊕ FurtherClasses → CountableOrdinal ⊕ FurtherClasses → Prop),
      (∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)) →
        ¬ adjoinPersistent.HasLogicalAgreement truth := by
  have hc : adjoinPersistent.HasCountableLosses := by
    refine ⟨fun ξ hξ ↦ ((tail_hasCountableLosses.countable_loss ξ hξ).image Sum.inl).mono ?_⟩
    rintro (x | y) ⟨h₁, h₂⟩
    · exact mem_image_of_mem _ ⟨h₁, h₂⟩
    · exact (h₂ (add_one_lt_omega_one hξ)).elim
  have hn : adjoinPersistent.HasNonemptyLosses := ⟨fun ξ hξ ↦
    have ⟨x, hx⟩ := tail_hasNonemptyLosses.nonempty_loss ξ hξ
    ⟨.inl x, hx⟩⟩
  exact ⟨hc, hn, aleph_one_lt_mk_sum, fun truth hsep ha ↦
    aleph_one_lt_mk_sum.ne' (adjoinPersistent.mk_eq_aleph_one hc hn ha hsep)⟩

/-! ### Countable losses are needed -/

/-- The tail domains with the further classes adjoined to the first domain only. -/
private def adjoinLost : ExpansionDomains (CountableOrdinal ⊕ FurtherClasses) where
  domain ξ := {z | Sum.elim (· ∈ tail.domain ξ) (fun _ ↦ ξ = 0) z}
  zero := eq_univ_of_forall fun
    | .inl x => by simp [tail.zero]
    | .inr _ => rfl
  antitone ξ _ h
    | .inl _, hx => tail.antitone h hx
    | .inr _, hx => le_antisymm (h.trans_eq hx) zero_le
  limit l hl hlt
    | .inl x, hx => tail.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ mem_iInter₂.1 hx ξ hξ)
    | .inr _, hx => by
      have h1 : (1 : Ordinal.{0}) < l := by
        simpa using hl.succ_lt (pos_iff_ne_zero.2 hl.ne_bot)
      exact absurd (mem_iInter₂.1 hx 1 h1) one_ne_zero
  domain_eq_empty_of_omega_one_le ξ h := eq_empty_of_forall_notMem fun
    | .inl x, hx => by simp [tail.domain_eq_empty_of_omega_one_le ξ h] at hx
    | .inr _, hx => (Ordinal.omega_pos 1).not_ge (h.trans_eq hx)

/-- **Countable losses cannot be dropped**: the domains with the further classes lost at the first
successor have nonempty losses and logical agreement for the observations "is the class `s`",
which separate the classes, and more than `ℵ₁` classes. -/
example : adjoinLost.HasNonemptyLosses ∧
    adjoinLost.HasLogicalAgreement (fun s z : CountableOrdinal ⊕ FurtherClasses ↦ z = s) ∧
    ℵ₁ < #(CountableOrdinal ⊕ FurtherClasses) ∧ ¬ adjoinLost.HasCountableLosses := by
  have hn : adjoinLost.HasNonemptyLosses := ⟨fun ξ hξ ↦
    have ⟨x, hx⟩ := tail_hasNonemptyLosses.nonempty_loss ξ hξ
    ⟨.inl x, hx⟩⟩
  have ha :
      adjoinLost.HasLogicalAgreement (fun s z : CountableOrdinal ⊕ FurtherClasses ↦ z = s) := by
    refine ⟨fun
      | .inl s => ⟨s.1 + 1, add_one_lt_omega_one s.2, uniform_eq ?_⟩
      | .inr _ => ⟨1, one_lt_omega_one, uniform_eq one_ne_zero⟩⟩
    exact notMem_tail_domain_add_one s
  exact ⟨hn, ha, aleph_one_lt_mk_sum, fun hc ↦
    aleph_one_lt_mk_sum.ne' (adjoinLost.mk_eq_aleph_one hc hn ha separates_eq)⟩

/-! ### Nonempty losses are needed -/

/-- A single class in every domain below `ω₁`. -/
private def constant : ExpansionDomains Unit where
  domain ξ := {_u | ξ < ω₁}
  zero := eq_univ_of_forall fun _ ↦ Ordinal.omega_pos 1
  antitone _ _ h _ hx := h.trans_lt hx
  limit _ _ hlt _ _ := hlt
  domain_eq_empty_of_omega_one_le _ h := eq_empty_of_forall_notMem fun _ hx ↦ h.not_gt hx

/-- **Nonempty losses cannot be dropped**: a single class in every domain below `ω₁` has countable
losses and logical agreement for the observations `z = s`, which separate its one class, and fewer
than `ℵ₁` classes. -/
example : constant.HasCountableLosses ∧
    constant.HasLogicalAgreement (fun s z : Unit ↦ z = s) ∧ #Unit < ℵ₁ ∧
    ¬ constant.HasNonemptyLosses :=
  ⟨⟨fun _ _ ↦ Set.to_countable _⟩,
    ⟨fun _ ↦ ⟨0, Ordinal.omega_pos 1, fun _ _ _ _ ↦ by simp⟩⟩,
    by simp [one_lt_aleph0.trans aleph0_lt_aleph_one],
    fun ⟨h⟩ ↦ by simpa [constant, one_lt_omega_one] using h 0 (Ordinal.omega_pos 1)⟩

/-! ### The least-level filtration -/

/-- The countable ordinals are uncountably many. -/
private theorem not_countable_countableOrdinal : ¬ Countable CountableOrdinal := by
  rw [← mk_le_aleph0_iff, mk_countableOrdinal, not_le]
  exact aleph0_lt_aleph_one

/-- The fibres of the identity rank on the countable ordinals are at most single ordinals. -/
private theorem countable_setOf_val_eq (α : Ordinal.{0}) (_ : α < ω₁) :
    {x : CountableOrdinal | x.1 = α}.Countable :=
  Subsingleton.countable fun _ ha _ hb ↦ Subtype.ext (ha.trans hb.symm)

/-- The tail domains of the countable ordinals as the filtration by a rank: the rank of a
countable ordinal is the ordinal itself. -/
private def tailOfRank : Filtration CountableOrdinal :=
  .ofRank (fun x ↦ x.1) (fun x ↦ x.2) countable_setOf_val_eq not_countable_countableOrdinal

/-- **The filtration by the rank is the filtration of the tail domains.** -/
example : tailOfRank = tail.toFiltration tail_hasCountableLosses tail_hasNonemptyLosses :=
  Filtration.ext fun _ _ ↦ rfl

/-- The persistent core of the filtration by the rank is empty. -/
example : tailOfRank.core = ∅ :=
  Filtration.core_ofRank

/-- The countable ordinals, each presented at its own level. -/
private def ownLevel : FullPresentations CountableOrdinal where
  presentedAt α := {x | x.1 = α}
  countable_presentedAt := countable_setOf_val_eq
  exists_mem_presentedAt x := ⟨x.1, x.2, rfl⟩
  presentedAt_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun x hx ↦ (h.trans hx.ge).not_gt x.2

/-- A class in the tail at `η` of the countable ordinals presented at their own levels is an
ordinal `≥ η`. -/
private theorem le_of_mem_ownLevel_tail {η : Ordinal.{0}} {x : CountableOrdinal}
    (hx : x ∈ ownLevel.tail η) : η ≤ x.1 :=
  not_lt.1 fun hlt ↦ hx (mem_iUnion₂.2 ⟨x.1, hlt, rfl⟩)

/-- **Full presentations with bounded comparison on `ℵ₁` classes**: for the truth predicate "the
class is below the quantifier rank of the sentence", a sentence of quantifier rank at most `η`
holds at no class of the tail at `η`. -/
example (L : Language.{0, 1}) :
    ownLevel.HasBoundedComparison fun (θ : L.Sentenceω) (p : CountableOrdinal) ↦ p.1 < θ.qrank :=
  ⟨fun _ _ _ hp _ hq _ hθ ↦ iff_of_false
    (fun h ↦ (h.trans_le hθ).not_ge (le_of_mem_ownLevel_tail hp))
    (fun h ↦ (h.trans_le hθ).not_ge (le_of_mem_ownLevel_tail hq))⟩

/-- **The least-level filtration of the countable ordinals is the filtration of the tail
domains**, and there are exactly `ℵ₁` countable ordinals, from the least-level filtration with its
empty core. -/
example : ownLevel.toFiltration not_countable_countableOrdinal =
      tail.toFiltration tail_hasCountableLosses tail_hasNonemptyLosses ∧
    #CountableOrdinal = ℵ₁ := by
  refine ⟨Filtration.ext fun η _ ↦ ?_,
    (ownLevel.toFiltration not_countable_countableOrdinal).mk_eq_aleph_one (by simp)⟩
  rw [ownLevel.domain_toFiltration]
  ext x
  refine ⟨le_of_mem_ownLevel_tail, fun h ↦ ?_⟩
  simp only [FullPresentations.tail, ownLevel, mem_compl_iff, mem_iUnion₂, not_exists]
  exact fun α hα hx ↦ (hx ▸ hα).not_ge h

/-! ### Noncollapse is needed -/

/-- A single class, presented at level `0`. -/
private def single : FullPresentations Unit where
  presentedAt α := {_x | α = 0}
  countable_presentedAt _ _ := Set.to_countable _
  exists_mem_presentedAt _ := ⟨0, Ordinal.omega_pos 1, rfl⟩
  presentedAt_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun _ hx ↦ (Ordinal.omega_pos 1).not_ge (h.trans_eq hx)

/-- **Noncollapse cannot be dropped**: a single class presented at level `0` has bounded comparison
for every truth predicate of the sentences of any language, and there is exactly one class. -/
example : (∀ {L : Language.{0, 1}} (truth : L.Sentenceω → Unit → Prop),
      single.HasBoundedComparison truth) ∧ #Unit = 1 ∧ #Unit < ℵ₁ :=
  ⟨fun _ ↦ ⟨fun _ _ p _ q _ _ _ ↦ by rw [Subsingleton.elim p q]⟩, mk_punit,
    by simp [one_lt_aleph0.trans aleph0_lt_aleph_one]⟩

/-! ### A prescribed age is needed -/

/-- The language of the unary relations `P n`, `n : ℕ`, with no functions. -/
private def unaryLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations
    | 1 => ℕ
    | _ => Empty

/-- The structure `M S` on `ℕ`: `P n` is everything for `n ∈ S` and nothing otherwise. -/
private abbrev unaryStructure (S : Set ℕ) : unaryLanguage.Structure ℕ where
  funMap f := Empty.elim f
  RelMap {n} r _ := match n, r with
    | 0, r => Empty.elim r
    | 1, k => k ∈ S
    | _ + 2, r => Empty.elim r

/-- **Every permutation is an automorphism of `M S`.** -/
example (S : Set ℕ) (σ : ℕ ≃ ℕ) :
    ∃ e : @Language.Equiv unaryLanguage ℕ ℕ (unaryStructure S) (unaryStructure S), ⇑e = σ :=
  ⟨@Language.Equiv.mk unaryLanguage ℕ ℕ (unaryStructure S) (unaryStructure S) σ
    (fun f ↦ Empty.elim f) (fun {n} r _ ↦ by
      rcases n with _ | _ | n
      exacts [r.elim, Iff.rfl, r.elim]), rfl⟩

/-- **The structures `M S` are pairwise nonisomorphic.** -/
example {S T : Set ℕ} (e : @Language.Equiv unaryLanguage ℕ ℕ (unaryStructure S)
    (unaryStructure T)) : S = T :=
  Set.ext fun k ↦ (@Language.Equiv.map_rel unaryLanguage ℕ ℕ (unaryStructure S)
    (unaryStructure T) e 1 k fun _ ↦ 0).symm

/-! ### Countably many back-and-forth classes are needed -/

open Language

private instance : unaryLanguage.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

private instance : Countable (Σ n, unaryLanguage.Relations n) := by
  refine @instCountableSigma _ _ _ fun n ↦ ?_
  rcases n with _ | _ | n
  exacts [inferInstanceAs (Countable Empty), inferInstanceAs (Countable ℕ),
    inferInstanceAs (Countable Empty)]

/-- The code on `ℕ` of the structure `M {k | x k = true}`. -/
private def unaryCode (x : ℕ → Bool) : StructureSpace unaryLanguage := fun q ↦
  match q with
  | ⟨⟨1, k⟩, _⟩ => x k
  | ⟨⟨0, r⟩, _⟩ => Empty.elim r
  | ⟨⟨_ + 2, r⟩, _⟩ => Empty.elim r

/-- The code of `M S` depends continuously on `S`. -/
private theorem continuous_unaryCode : Continuous unaryCode := by
  refine continuous_pi fun q ↦ ?_
  rcases q with ⟨⟨_ | _ | n, r⟩, v⟩
  exacts [r.elim, continuous_apply r, r.elim]

/-- Isomorphic codes `unaryCode x` and `unaryCode y` have `x = y`. -/
private theorem eq_of_unaryCode {x y : ℕ → Bool}
    (h : (structureIsoSetoid unaryLanguage).r (unaryCode x) (unaryCode y)) : x = y := by
  obtain ⟨e⟩ := h
  funext k
  exact Bool.eq_iff_iff.mpr (@Language.Equiv.map_rel unaryLanguage ℕ ℕ
    (unaryCode x).toStructure (unaryCode y).toStructure e 1 k fun _ ↦ 0).symm

/-- **Countably many back-and-forth classes cannot be dropped**: the codes of the structures
`M S` form a nonempty perfect set of pairwise nonisomorphic codes, so the set of all codes of this
language is not thin, and at some level `η < ω₁` they fall into uncountably many classes of
back-and-forth equivalence (`isThinOn_of_countable_bfClasses`). -/
example : ¬ IsThinOn (structureIsoSetoid unaryLanguage) univ ∧
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧ ¬ Countable (Quotient
      ((codeBFEquivSetoid unaryLanguage η).comap
        (Subtype.val : ↥(univ : Set (StructureSpace unaryLanguage)) → _))) := by
  have hthin : ¬ IsThinOn (structureIsoSetoid unaryLanguage) univ := by
    exact not_not.mpr (HasCantorAntichainOn.hasPerfectAntichainOn ⟨unaryCode,
      continuous_unaryCode, fun _ ↦ mem_univ _, fun _ _ hxy h ↦ hxy (eq_of_unaryCode h)⟩)
  refine ⟨hthin, ?_⟩
  by_contra! h
  exact hthin (isThinOn_of_countable_bfClasses h)

/-! ### The density sentence -/

/-- The sharp comparison (agreement on the sentences of quantifier rank at most the stage) gives
logical agreement for the classes of the density sentence. -/
example (D : ExpansionDomains DensityClass)
    (h : ∀ η, η < ω₁ → ∀ p ∈ D.domain η, ∀ q ∈ D.domain η, ∀ θ : baseLanguage.Sentenceω,
      θ.qrank ≤ η → (densityTruth θ p ↔ densityTruth θ q)) :
    D.HasLogicalAgreement densityTruth :=
  .of_qrank_le h

/-- The cap-to-model theorem at `ω`, for the carriers of `Type 1`, from the coatom extension
property with apex at `ω`: the models of the density sentence there are infinite. -/
example (hext : StageType.HasApexCoatomExtensions.{0} ω) {M : Type 1}
    [baseLanguage.{0}.Structure M] (h : baseLanguage.densitySentence.Realize M) : Infinite M :=
  (CapToModel.of_hasApexCoatomExtensions.{1} hext).infinite h

end Examples

end VaughtConjecture.MainTheorem

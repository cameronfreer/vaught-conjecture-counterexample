/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Language

/-!
# Density at an ordinal and the classes `K_β[L]`

Numbering as in the current draft of [AFK26].

**Raw truncation up to renaming** (correspondence with the printed definitions).  [AFK26,
Definition 4.10]: `trunc_α(t) = (c, Σ, trunc_α ∘ p)`, where `trunc_α` keeps a label below `α` and
sends every other ordinal label to `∞` (`Label.reduce α`); [AFK26, Definition 4.6]:
`t₀ ≅_ren t₁` when `t₁` is the renaming of `t₀` along a bijection of cells.  For a successor `α`
the truncated labelling need not be lawful, so `trunc_α(t)` is in general not a stage type; the
comparison is therefore made on the raw labellings, never by stage reduction:
`StageType.IsTruncRenaming α s u` says that some renaming `s'` of `s` has the frame and rows of
`u` (`s'.toScheme = u.toScheme`) and, cell by cell, `trunc_α` of the label of `s'` is `trunc_α`
of the label of `u`.  This is `trunc_α(s) ≅_ren trunc_α(u)`, since truncation commutes with
renaming (both act on labels cell by cell).  No hypothesis on `α`: every ordinal, successors
included.

**Classes** (native construction).  `TemplateClass.LiftRel P c d` holds when some
representatives of `c` and `d` have the same scheme and labels related by `P` cell by cell.  For
fixed representatives it is "some renaming of the first is so related to the second"
(`TemplateClass.liftRel_toClass_iff`), the one lemma behind both class relations used here:

* `TemplateClass.TruncEquiv α c d`, raw truncation at `α` up to renaming
  (`TemplateClass.truncEquiv_toClass_iff`: on representatives it is `IsTruncRenaming α`, so it
  does not depend on the representatives the template system `L` chooses);
* `TemplateClass.ObservesAt x q D`, the observation of `D` at a cutoff `x` up to renaming
  (`TemplateClass.observesAt_toClass_iff`: on representatives it is membership of a renaming of
  `q` in `receivingFamily D x`).

**Density** `D[α]` [AFK26, Definition 4.20] (correspondence with the printed definitions):
`SatisfiesDensityAt α G`, for every ordinal `α`, with one quantifier for each printed one.

**The class `K_β[L]`** [AFK26, Definition 4.21] (correspondence with the printed definitions):
`templateStageClass β M`, the structures on `M` that are compatible with `ID[L]`, fixed by
`τ_β`, and satisfy `D[α]` for every `α < ω + ω · β`.  Nonemptiness of the carrier, the printed
convention of [AFK26, §1] ("all structures will be countable with non-empty domains"), is the
first clause.  Countability is not part of the class: statements that need it carry
`[Countable M]`.  The printed range `β ∈ ω₁` is a hypothesis of the statements that use it.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Labels related cell by cell, and raw truncation up to renaming -/

namespace StageType

variable {γ : Ordinal.{u}} {n : ℕ}

/-- **The same scheme, with labels related cell by cell by `P`.**  Native construction. -/
def LabelRel (P : Label.{u} → Label.{u} → Prop) (s u : StageType.{u} γ n) : Prop :=
  s.toScheme = u.toScheme ∧
    ∀ (i : Fin s.card) (j : Fin u.card), (i : ℕ) = j → P (s.label i) (u.label j)

/-- **Renaming both sides along one bijection keeps the relation.**  Native construction. -/
theorem LabelRel.exists_renameCells {P : Label.{u} → Label.{u} → Prop} {s u : StageType.{u} γ n}
    (h : s.LabelRel P u) {k : ℕ} (π : Fin k ≃ Fin u.card) :
    ∃ π' : Fin k ≃ Fin s.card, (s.renameCells π').LabelRel P (u.renameCells π) := by
  obtain ⟨hS, hl⟩ := h
  obtain ⟨⟨c, C, R⟩, p, _, _, _, _⟩ := s
  obtain ⟨⟨c', C', R'⟩, p', _, _, _, _⟩ := u
  obtain ⟨rfl, hC, hR⟩ := Scheme.mk.inj hS
  obtain rfl := eq_of_heq hC
  obtain rfl := eq_of_heq hR
  exact ⟨π, rfl, fun i j hij ↦ hl (π i) (π j) (by rw [Fin.ext hij])⟩

/-- **Raw truncation at `α` up to renaming** ([AFK26, Definitions 4.6 and 4.10]):
`trunc_α(s) ≅_ren trunc_α(u)`.  Some renaming of `s` has the frame and rows of `u`, and `trunc_α`
of its labels are those of `u`, cell by cell.  The truncated labellings are compared as raw
labellings; no truncated stage type is formed, and `α` is any ordinal.
Correspondence with the printed definitions. -/
def IsTruncRenaming (α : Ordinal.{u}) (s u : StageType.{u} γ n) : Prop :=
  ∃ s', s.IsCellRenaming s' ∧ s'.LabelRel (fun a b ↦ Label.reduce α a = Label.reduce α b) u

end StageType

namespace TemplateClass

open StageType

variable {γ : Ordinal.{u}} {n : ℕ}

/-- **Classes related cell by cell by `P`**: some representatives have the same scheme and labels
related by `P`.  Native construction. -/
def LiftRel (P : Label.{u} → Label.{u} → Prop) (c d : TemplateClass.{u} γ n) : Prop :=
  ∃ s u : StageType.{u} γ n, s.toClass = c ∧ u.toClass = d ∧ s.LabelRel P u

/-- **On representatives, the relation of classes is "some renaming of the first is related to
the second"**: it does not depend on the representative of the second class.
Native construction. -/
theorem liftRel_toClass_iff {P : Label.{u} → Label.{u} → Prop} {s u : StageType.{u} γ n} :
    LiftRel P s.toClass u.toClass ↔ ∃ s', s.IsCellRenaming s' ∧ s'.LabelRel P u := by
  constructor
  · rintro ⟨s₁, u₁, hs, hu, h⟩
    obtain ⟨k, π, rfl⟩ := toClass_eq_toClass_iff.mp hu
    obtain ⟨π', h'⟩ := h.exists_renameCells π
    exact ⟨_, (toClass_eq_toClass_iff.mp hs).symm.trans ⟨_, π', rfl⟩, h'⟩
  · rintro ⟨s', hs', h⟩
    exact ⟨s', u, (toClass_eq_toClass_iff.mpr hs').symm, rfl, h⟩

/-- **Raw truncation at `α` up to renaming, on classes** ([AFK26, Definitions 4.6 and 4.10]).
Correspondence with the printed definitions. -/
def TruncEquiv (α : Ordinal.{u}) (c d : TemplateClass.{u} γ n) : Prop :=
  LiftRel (fun a b ↦ Label.reduce α a = Label.reduce α b) c d

/-- **On representatives, `TruncEquiv` is `trunc_α(s) ≅_ren trunc_α(u)`.**
Correspondence with the printed definitions. -/
theorem truncEquiv_toClass_iff {α : Ordinal.{u}} {s u : StageType.{u} γ n} :
    s.toClass.TruncEquiv α u.toClass ↔ s.IsTruncRenaming α u :=
  liftRel_toClass_iff

/-- **The observation of `D` at a cutoff `x`, up to renaming**: some representatives have the same
scheme and agree after capping at `x`.  Native construction. -/
def ObservesAt (x : Label.{u}) (q D : TemplateClass.{u} γ n) : Prop :=
  LiftRel (fun a b ↦ min a x = min b x) q D

/-- **On representatives, `ObservesAt` is membership of a renaming in the receiving family.**
Native construction. -/
theorem observesAt_toClass_iff {x : Label.{u}} {q D : StageType.{u} γ n} :
    q.toClass.ObservesAt x D.toClass ↔ ∃ q', q.IsCellRenaming q' ∧ q' ∈ receivingFamily D x :=
  liftRel_toClass_iff

end TemplateClass

/-! ### Density -/

variable {M : Type v}

open Correspondence in
/-- **Density `D[α]`** [AFK26, Definition 4.20], for every ordinal `α` (successors included).  One
quantifier for each printed one:

* "for each `(Q_u(xy), Q_t(x)) ∈ ID[T]` with `u, t ∈ T`": legal classes `t` on `n ≥ 1` points
  and `u` on `n + m` points (`m ≥ 0`) with the pair `(Q_u(x y), Q_t(x))` in `ID[L]`, the first
  `n` variables being `x` (`Fin.castAdd m`).  The donor `u` has any rank: its labels are any
  ordinals below `ω₁`;
* "`∀ x (Q_t(x) → …`": every `x : Fin n → M` with `G ⊨ Q_t(x)`;
* "`∃ y ⋁_{s ∈ T, trunc_α(s) ≅_ren trunc_α(u)} Q_s(xy)`": some `y : Fin m → M` and a legal class
  `s` on `n + m` points with `trunc_α(s) ≅_ren trunc_α(u)` (`TemplateClass.TruncEquiv`, raw
  truncation up to renaming, not stage reduction) and `G ⊨ Q_s(x y)` (`Fin.append x y`).
Correspondence with the printed definitions. -/
def SatisfiesDensityAt (α : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)),
    (⟨n + m, TemplateSymbol.invariant u (Nat.lt_add_right m hn),
      atom (L := templateLanguage) (TemplateSymbol.invariant t hn) (Fin.castAdd m)⟩ :
        DiagramPair templateLanguage.{u}) ∈ templateDiagramPairs →
    ∀ x : Fin n → M, RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant t hn) x →
      ∃ (y : Fin m → M) (s : LegalClass.{u} (n + m)), s.1.TruncEquiv α u.1 ∧
        RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant s (Nat.lt_add_right m hn))
          (Fin.append x y)

/-- The premise of `D[α]` is the truth of `Q_t` on the first `n` places of the template of
class `u` (`mk_atom_mem_templateDiagramPairs_iff`).
Correspondence with the printed definitions. -/
theorem satisfiesDensityAt_iff (α : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    SatisfiesDensityAt α G ↔
      ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)),
        u.1.Holds (TemplateSymbol.invariant t hn) (Fin.castAdd m) →
        ∀ x : Fin n → M, RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant t hn) x →
          ∃ (y : Fin m → M) (s : LegalClass.{u} (n + m)), s.1.TruncEquiv α u.1 ∧
            RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant s (Nat.lt_add_right m hn))
              (Fin.append x y) := by
  simp only [SatisfiesDensityAt, mk_atom_mem_templateDiagramPairs_iff]

/-! ### The classes `K_β[L]` -/

variable (M) in
/-- **The class `K_β[L]`** [AFK26, Definition 4.21], one clause for each printed clause, after
the convention of nonempty carriers:

* `Nonempty M`: the convention of [AFK26, §1], "all structures will be countable with non-empty
  domains" (countability is carried by the statements that use it);
* "`M` is compatible with `ID[T]`": `IsTemplateCompatible G` ([AFK26, Definitions 2.5 and 4.18]);
* "`τ_β(M) = M`": `projectStructure β G = G` ([AFK26, Definitions 2.7 and 4.16]);
* "`M ⊨ D[α]` for all `α < ω + ω · β`": `SatisfiesDensityAt α G` for every `α < blockStage β`
  ([AFK26, Definition 4.20]).  Correspondence with the printed definitions. -/
def templateStageClass (β : Ordinal.{u}) : Set (templateLanguage.{u}.Structure M) :=
  {G | Nonempty M ∧ IsTemplateCompatible G ∧ projectStructure β G = G ∧
    ∀ α < blockStage β, SatisfiesDensityAt α G}

/-- A structure of `K_β[L]` has a nonempty carrier.  Correspondence with the printed definitions. -/
theorem nonempty_of_mem_templateStageClass {β : Ordinal.{u}} {G : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M β) : Nonempty M :=
  hG.1

/-- A structure of `K_β[L]` is fixed by `τ_β`, so `β` is a fixing stage when `β < ω₁`.
Correspondence with the printed definitions. -/
theorem mem_fixingStages_of_mem_templateStageClass {β : Ordinal.{u}}
    {G : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M β) (hβ : β < ω₁) :
    β ∈ fixingStages G :=
  ⟨hβ, hG.2.2.1⟩

end

end VaughtConjecture

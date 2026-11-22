/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.LegalSystem

/-!
# Chosen representatives and the symbols of a chart: one face

Numbering as in the current draft of [AFK26].  The printed language `L_b[L]` of
[AFK26, Definition 4.15] names its symbols `Q_t` by the templates `t` of the template system `L`,
one in each cell-renaming class ([AFK26, Definition 4.11]), and the chart of a template `t ∈ L`
([AFK26, Definition 4.18], second clause) lets `Q_{t*}` hold of `x_{i_0}, …, x_{i_{k-1}}` when the
restriction of `t` to `{i_j}`, transported along `i_j ↦ j`, is a cell renaming of `t*`.  The
library's `templateLanguage` names the same symbol by the class of `t*`
(`TemplateSymbol.invariant`), and `StageType.Holds` reads it through the class at `ω₁` of the face.
Here the choice of `L` is `chosenTemplateRepresentative`, written `r(c)` below.

**The printed reading** (`StageType.PrintedHolds`).  `T.PrintedHolds t xs`: `xs` is injective,
the face of `T` along `xs` is defined, and it is a cell renaming of the template `t`, which keeps
its cell names.  The printed restriction `t↾A₀` keeps the cells of `t`; the positional face
`StageType.restrictFace` numbers them by position.  The two differ by a renaming, which the
reading absorbs.  A structure `Q` on a carrier `M` with one relation for every template **realizes
the printed chart** of `T` at a tuple `x` (`RealizesPrintedChart`) when every `Q t` holds of
`x ∘ xs` exactly when `T.PrintedHolds t xs`; only the symbols `Q_t` are read, not `P_k` or `R_t`.
The printed reading is a reading of classes, with no legality hypothesis
(`StageType.printedHolds_iff_toClass`): it depends only on the class of the chart's type
(`StageType.printedHolds_congr_of_toClass_eq`) and passes along faces with the point map fixed
(`StageType.printedHolds_comp_iff`).

**One face.**  Fix a class `c` on `[n]` and a point embedding `f : Fin m ↪ Fin n` along which `c`
has the face class `d` (`TemplateClass.restrictFace`).  The literal face `s` of `r(c)` along `f`
and the chosen `r(d)` lie in the class `d`, but their cells are named separately.

* `RepresentativeFaceTarget` — the face of `r(c)` along `f` is defined, is some `s` of class `d`,
  and an explicit bijection of cells `σ` renames `s` to `r(d)`.  **Proved**
  (`representativeFaceTarget`).
* `FacePredicateSquareTarget` — one predicate on the subtuple `x ∘ f`: if `x` realizes the printed
  chart of `r(c)`, then `Q_s` and `Q_{r(d)}` have the same truth value at `x ∘ f`.  **Proved**
  (`facePredicateSquareTarget`): both hold, since `s` is the face and `σ` renames it to `r(d)`.
* `FaceChartSquareTarget` — every template predicate on subtuples of the face: the printed chart of
  `r(c)` along `f`, the printed chart of `s` and the printed chart of `r(d)` agree, with the point
  map `f` and the subtuples fixed.  **Proved** (`faceChartSquareTarget`).
* `FaceOccurrenceSquareTarget` — its form at a tuple: if `x` realizes the printed chart of `r(c)`,
  then `x ∘ f` realizes the printed chart of `s` and that of `r(d)`.  **Proved**
  (`faceOccurrenceSquareTarget`).
* `PrintedClassReadingTarget` — the printed reading of `Q_t` is the class reading of the symbol
  `Q_{[t]}` of `templateLanguage`, at stage `ω₁`, for a strongly coded legal `t`.  **Proved**
  (`printedClassReadingTarget`).

**The class reading.**  In `templateLanguage` the face symbol read through `s` and through `r(d)`
is one symbol, `Q_d`, since `s.toClass = d = r(d).toClass`; there the square is the identity of
symbols, and its form for every predicate is `StageType.holds_comp_iff`.  Cell names enter only in
the printed reading, which is why the targets are stated for `PrintedHolds`.
-/

universe u v

namespace VaughtConjecture

open Finset Ordinal

noncomputable section

/-! ### The printed reading of a template predicate -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **The printed reading of `Q_t` in the chart of `T`** ([AFK26, Definition 4.18], second
clause): `xs` is injective, the face of `T` along `xs` is defined, and the face is a cell renaming
of the template `t`.  The symbol is indexed by the template `t` itself, with its cell names; the
point map `xs` transports the face onto the underlying set of `t`.
Correspondence with the printed definitions. -/
def PrintedHolds (T : StageType.{u} α n) (t : StageType.{u} α k) (xs : Fin k → Fin n) : Prop :=
  ∃ h : Function.Injective xs, ∃ s, restrictFace ⟨xs, h⟩ T = some s ∧ s.IsCellRenaming t

/-- **The printed reading is a reading of classes**: `Q_t` holds of `xs` in the printed chart of
`T` exactly when `xs` is injective and the face of `T` along `xs` has the class of `t`.  No
legality and no positive arity is assumed. -/
theorem printedHolds_iff_toClass (T : StageType.{u} α n) (t : StageType.{u} α k)
    (xs : Fin k → Fin n) :
    T.PrintedHolds t xs ↔
      ∃ h : Function.Injective xs, (restrictFace ⟨xs, h⟩ T).map toClass = some t.toClass := by
  refine exists_congr fun h ↦ ⟨fun ⟨s, hs, hst⟩ ↦ ?_, fun hm ↦ ?_⟩
  · rw [hs, Option.map_some, toClass_eq_toClass_iff.mpr hst]
  · obtain ⟨s, hs, hst⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨s, hs, toClass_eq_toClass_iff.mp hst⟩

/-- **The printed reading depends only on the class of the chart's type**: stage types of one
class have the same printed charts, with the same tuples. -/
theorem printedHolds_congr_of_toClass_eq {T T' : StageType.{u} α n} (hT : T.toClass = T'.toClass)
    (t : StageType.{u} α k) (xs : Fin k → Fin n) : T.PrintedHolds t xs ↔ T'.PrintedHolds t xs := by
  rw [printedHolds_iff_toClass, printedHolds_iff_toClass]
  refine exists_congr fun h ↦ ?_
  rw [← TemplateClass.restrictFace_toClass, ← TemplateClass.restrictFace_toClass, hT]

/-- **The printed reading along a face**: if the face of `T` along `f` is `s`, `Q_t` holds of
`f ∘ ys` in the printed chart of `T` exactly when it holds of `ys` in the printed chart of `s`
(`restrictFace_trans`).  The point map `f` and the tuple `ys` are not changed. -/
theorem printedHolds_comp_iff {T : StageType.{u} α n} {s : StageType.{u} α m}
    {f : Fin m ↪ Fin n} (hf : restrictFace f T = some s) (t : StageType.{u} α k)
    (ys : Fin k → Fin m) : T.PrintedHolds t (f ∘ ys) ↔ s.PrintedHolds t ys := by
  constructor
  · rintro ⟨h, hx⟩
    have hys : Function.Injective ys := h.of_comp
    have heq : restrictFace ⟨f ∘ ys, h⟩ T = restrictFace ⟨ys, hys⟩ s :=
      (restrictFace_trans T f ⟨ys, hys⟩ hf).symm
    rw [heq] at hx
    exact ⟨hys, hx⟩
  · rintro ⟨h, hx⟩
    have hfy : Function.Injective (f ∘ ys) := f.injective.comp h
    have heq : restrictFace ⟨f ∘ ys, hfy⟩ T = restrictFace ⟨ys, h⟩ s :=
      (restrictFace_trans T f ⟨ys, h⟩ hf).symm
    refine ⟨hfy, ?_⟩
    rw [heq]
    exact hx

end StageType

open StageType

/-- **A tuple realizes the printed chart of `T` on the symbols `Q_t`**: this reads only the
symbols `Q_t` of [AFK26, Definition 4.18] (its second clause); the clauses for `P_k` and `R_t` are
separate and not read here.  In a structure `Q` with one relation for every template
([AFK26, Definitions 4.18 and 4.31]), every `Q t` holds of `x ∘ xs` exactly when
`T.PrintedHolds t xs`.  Correspondence with the printed definitions. -/
def RealizesPrintedChart {M : Type v} {n : ℕ}
    (Q : ∀ ⦃k : ℕ⦄, StageType.{u} ω₁ k → (Fin k → M) → Prop) (x : Fin n → M)
    (T : StageType.{u} ω₁ n) : Prop :=
  ∀ ⦃k : ℕ⦄ (t : StageType.{u} ω₁ k) (xs : Fin k → Fin n), Q t (x ∘ xs) ↔ T.PrintedHolds t xs

/-! ### The face of a chosen representative -/

/-- **Target: the face of a chosen representative and the chosen representative of the face.**
If the class `c` has the face class `d` along `f`, the face of `r(c)` along `f` is defined and is a
stage type `s` of class `d`, and an explicit bijection of cells `σ` renames `s` to `r(d)`.  The
point map `f` is not changed; `σ` is needed because `r(c)` and `r(d)` are chosen separately.
Correspondence with the printed definitions. -/
def RepresentativeFaceTarget : Prop :=
  ∀ ⦃n m : ℕ⦄ (c : TemplateClass.{u} ω₁ n) (d : TemplateClass.{u} ω₁ m) (f : Fin m ↪ Fin n),
    c.restrictFace f = some d →
      ∃ s : StageType.{u} ω₁ m, restrictFace f (chosenTemplateRepresentative c) = some s ∧
        s.toClass = d ∧ ∃ σ : Fin (chosenTemplateRepresentative d).card ≃ Fin s.card,
          s.renameCells σ = chosenTemplateRepresentative d

/-- **The face of a chosen representative and the chosen representative of the face, proved**:
by `TemplateClass.restrictFace_toClass` and `toClass_chosenTemplateRepresentative`. -/
theorem representativeFaceTarget : RepresentativeFaceTarget.{u} := by
  intro n m c d f h
  have h' : (chosenTemplateRepresentative c).toClass.restrictFace f = some d := by
    rw [toClass_chosenTemplateRepresentative]
    exact h
  rw [TemplateClass.restrictFace_toClass] at h'
  obtain ⟨s, hs, hsd⟩ := Option.map_eq_some_iff.mp h'
  have hren : s.IsCellRenaming (chosenTemplateRepresentative d) := by
    rw [← toClass_eq_toClass_iff, toClass_chosenTemplateRepresentative]
    exact hsd
  obtain ⟨k, σ, hσ⟩ := hren
  obtain rfl : k = (chosenTemplateRepresentative d).card := by
    rw [← hσ]
    rfl
  exact ⟨s, hs, hsd, σ, hσ⟩

/-! ### The semantic square on one face -/

/-- **Target: one face predicate, read through the literal face or through the chosen
representative.**  If `c` has the face class `d` along `f`, `s` is the face of `r(c)` along `f`,
and `x` realizes the printed chart of `r(c)` in `Q`, then `Q_s` and `Q_{r(d)}` have the same truth
value at the literal subtuple `x ∘ f`.  The point map `f` and the tuple `x` are fixed; only the
cell names of the index change.  Correspondence with the printed definitions. -/
def FacePredicateSquareTarget : Prop :=
  ∀ ⦃n m : ℕ⦄ (c : TemplateClass.{u} ω₁ n) (d : TemplateClass.{u} ω₁ m) (f : Fin m ↪ Fin n)
    (s : StageType.{u} ω₁ m), c.restrictFace f = some d →
      restrictFace f (chosenTemplateRepresentative c) = some s →
        ∀ {M : Type v} (Q : ∀ ⦃k : ℕ⦄, StageType.{u} ω₁ k → (Fin k → M) → Prop)
          (x : Fin n → M), RealizesPrintedChart Q x (chosenTemplateRepresentative c) →
            (Q s (x ∘ f) ↔ Q (chosenTemplateRepresentative d) (x ∘ f))

/-- **One face predicate, read through the literal face or through the chosen representative,
proved**: both readings hold, `Q_s` because `s` is the face and `Q_{r(d)}` by the renaming of
`representativeFaceTarget`. -/
theorem facePredicateSquareTarget : FacePredicateSquareTarget.{u, v} := by
  intro n m c d f s hcd hs M Q x hx
  obtain ⟨s', hs', -, σ, hσ⟩ := representativeFaceTarget c d f hcd
  have hss' : s' = s := Option.some_injective _ (hs'.symm.trans hs)
  have hren : s'.IsCellRenaming (chosenTemplateRepresentative d) := ⟨_, σ, hσ⟩
  rw [hss'] at hren
  have hface : restrictFace ⟨f, f.injective⟩ (chosenTemplateRepresentative c) = some s := hs
  exact iff_of_true ((hx s f).mpr ⟨f.injective, s, hface, StageType.IsCellRenaming.refl s⟩)
    ((hx _ f).mpr ⟨f.injective, s, hface, hren⟩)

/-- **Target: the printed charts of the literal face and of the chosen representative agree.**  If
`c` has the face class `d` along `f` and `s` is the face of `r(c)` along `f`, then for every
template `t` on `[k]` and every `ys : Fin k → Fin m`, `Q_t` holds of `f ∘ ys` in the printed chart
of `r(c)` exactly when it holds of `ys` in the printed chart of `s`, and exactly when it holds of
`ys` in the printed chart of `r(d)`.  The point map `f` and the subtuple `ys` are fixed; the
charts of `s` and of `r(d)` differ only by the names of cells.  Proved
(`faceChartSquareTarget`).
Correspondence with the printed definitions. -/
def FaceChartSquareTarget : Prop :=
  ∀ ⦃n m : ℕ⦄ (c : TemplateClass.{u} ω₁ n) (d : TemplateClass.{u} ω₁ m) (f : Fin m ↪ Fin n)
    (s : StageType.{u} ω₁ m), c.restrictFace f = some d →
      restrictFace f (chosenTemplateRepresentative c) = some s →
        ∀ ⦃k : ℕ⦄ (t : StageType.{u} ω₁ k) (ys : Fin k → Fin m),
          ((chosenTemplateRepresentative c).PrintedHolds t (f ∘ ys) ↔ s.PrintedHolds t ys) ∧
            (s.PrintedHolds t ys ↔ (chosenTemplateRepresentative d).PrintedHolds t ys)

/-- **The printed charts of the literal face and of the chosen representative agree, proved**:
the first equivalence is `StageType.printedHolds_comp_iff`, the second
`StageType.printedHolds_congr_of_toClass_eq`, since `s` and `r(d)` have the class `d`. -/
theorem faceChartSquareTarget : FaceChartSquareTarget.{u} := by
  intro n m c d f s hcd hs k t ys
  obtain ⟨s', hs', hsd, -⟩ := representativeFaceTarget c d f hcd
  have hss' : s' = s := Option.some_injective _ (hs'.symm.trans hs)
  rw [hss'] at hsd
  refine ⟨printedHolds_comp_iff hs t ys, printedHolds_congr_of_toClass_eq ?_ t ys⟩
  rw [toClass_chosenTemplateRepresentative]
  exact hsd

/-- **Target: the semantic square at a tuple.**  If `c` has the face class `d` along `f`, `s` is
the face of `r(c)` along `f`, and `x` realizes the printed chart of `r(c)` in `Q`, then the literal
subtuple `x ∘ f` realizes the printed chart of `s` and the printed chart of `r(d)`.  Proved
(`faceOccurrenceSquareTarget`).
Correspondence with the printed definitions. -/
def FaceOccurrenceSquareTarget : Prop :=
  ∀ ⦃n m : ℕ⦄ (c : TemplateClass.{u} ω₁ n) (d : TemplateClass.{u} ω₁ m) (f : Fin m ↪ Fin n)
    (s : StageType.{u} ω₁ m), c.restrictFace f = some d →
      restrictFace f (chosenTemplateRepresentative c) = some s →
        ∀ {M : Type v} (Q : ∀ ⦃k : ℕ⦄, StageType.{u} ω₁ k → (Fin k → M) → Prop)
          (x : Fin n → M), RealizesPrintedChart Q x (chosenTemplateRepresentative c) →
            RealizesPrintedChart Q (x ∘ f) s ∧
              RealizesPrintedChart Q (x ∘ f) (chosenTemplateRepresentative d)

/-- **The semantic square at a tuple, proved**: `faceChartSquareTarget` at the literal subtuple
`x ∘ f`. -/
theorem faceOccurrenceSquareTarget : FaceOccurrenceSquareTarget.{u, v} := by
  intro n m c d f s hcd hs M Q x hx
  have hsq := faceChartSquareTarget c d f s hcd hs
  exact ⟨fun k t ys ↦ (hx t (f ∘ ys)).trans (hsq t ys).1,
    fun k t ys ↦ ((hx t (f ∘ ys)).trans (hsq t ys).1).trans (hsq t ys).2⟩

/-! ### The printed reading and the class reading -/

/-- **Target: the printed reading of `Q_t` is the class reading of `Q_{[t]}`.**  At stage `ω₁`,
for a strongly coded legal template `t` on `[k]` with `0 < k`, `Q_t` holds of `xs` in the printed
chart of `T` exactly when the symbol `TemplateSymbol.invariant` of the class of `t` holds of `xs`
in the chart `StageType.Holds` of `T`.  Proved (`printedClassReadingTarget`).
Correspondence with the printed definitions. -/
def PrintedClassReadingTarget : Prop :=
  ∀ ⦃n k : ℕ⦄ (T : StageType.{u} ω₁ n) (t : StageType.{u} ω₁ k) (ht : t.IsStronglyCodedLegal)
    (hk : 0 < k) (xs : Fin k → Fin n),
      T.PrintedHolds t xs ↔ T.Holds
        (TemplateSymbol.invariant ⟨t.toClass, (TemplateClass.isStronglyCodedLegal_toClass t).mpr ht⟩
          hk) xs

/-- **The printed reading of `Q_t` is the class reading of `Q_{[t]}`, proved**: at stage `ω₁` the
class at `ω₁` of a face is its class, and two stage types have one class exactly when they are
cell renamings of each other (`StageType.toClass_eq_toClass_iff`).  The legal positive-arity
specialization of `StageType.printedHolds_iff_toClass`. -/
theorem printedClassReadingTarget : PrintedClassReadingTarget.{u} := by
  intro n k T t ht hk xs
  have hg (s : StageType.{u} ω₁ k) : s.globalClass = s.toClass := by
    rw [globalClass, reduce_eq_castLE _ _ le_rfl, castLE_refl]
  refine exists_congr fun h ↦ exists_congr fun s ↦ and_congr_right fun _ ↦ ?_
  change s.IsCellRenaming t ↔ s.globalClass = t.toClass
  rw [hg, toClass_eq_toClass_iff]

end

end VaughtConjecture

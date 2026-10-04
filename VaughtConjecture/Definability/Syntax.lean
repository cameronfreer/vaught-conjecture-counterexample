/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.QuantifierRank
import InfinitaryLogic.Scott.Formula

/-!
# Existential closure of the last free variables, and extension formulas

Roadmap, Layer 0 (general results with no construction imports); the quantitative reconstruction
pathway of `roadmap/COMPANIONS.md`, row 1 (the syntax of the successor step).

Three operations on infinitary formulas `L.Formulaω`, for an arbitrary language `L`, with their
semantics and their quantifier rank (`BoundedFormulaω.qrank`):

* **Existential closure of the last `m` free variables** (`existsLastVars m φ`, for
  `φ : L.Formulaω (Fin (k + m))`): `m` applications of `existsLastVar`.  It is realized at `v`
  exactly when `φ` is realized at `v` extended by some `ys : Fin m → N` (`realize_existsLastVars`),
  and it adds exactly `m` to the quantifier rank (`qrank_existsLastVars`).
* **Renaming free variables** keeps the quantifier rank, and a conjunction `φ ⊓ ψ` has the larger
  of the two ranks: InfinitaryLogic's `BoundedFormulaω.qrank_mapFreeVars` (made a `simp` lemma
  here) and `BoundedFormulaω.qrank_inf`.
* **The extension formula** (`extendFormula ψ f`, for `ψ : L.Formulaω (Fin m)` and
  `f : Fin k → Fin m`): `∃ z̄ (ψ(z̄) ∧ ⋀_{i < k} z_{f i} = x_i)`.  It holds of a tuple `c` exactly
  when `c` extends along `f` to a tuple realizing `ψ` (`realize_extendFormula`), and its rank is
  that of `ψ` plus `m` (`qrank_extendFormula`).  The conjunction of equations is finite and has
  rank `0`.

Every statement here holds for an arbitrary language and imports nothing from the construction;
each is a candidate for upstreaming to InfinitaryLogic.

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe u v w

namespace FirstOrder.Language

open Structure BoundedFormulaω

variable {L : Language.{u, v}} {k m : ℕ}

/-! ### Renaming free variables -/

attribute [simp] BoundedFormulaω.qrank_mapFreeVars

/-! ### Existential closure of the last free variables -/

/-- **Existential closure of the last `m` free variables**: `∃ y_{m-1} … ∃ y_0`, by `m`
applications of `existsLastVar`.  A candidate for upstreaming to InfinitaryLogic. -/
def existsLastVars : ∀ m : ℕ, L.Formulaω (Fin (k + m)) → L.Formulaω (Fin k)
  | 0, φ => φ
  | m + 1, φ => existsLastVars m (existsLastVar φ)

@[simp]
theorem existsLastVars_zero (φ : L.Formulaω (Fin (k + 0))) : existsLastVars 0 φ = φ :=
  rfl

theorem existsLastVars_succ (φ : L.Formulaω (Fin (k + (m + 1)))) :
    existsLastVars (m + 1) φ = existsLastVars m (existsLastVar φ) :=
  rfl

/-- **Semantics of the existential closure**: `∃ ȳ φ(x̄, ȳ)` holds at `v` exactly when `φ` holds
at `v` followed by some `ys`.  A candidate for upstreaming to InfinitaryLogic. -/
theorem realize_existsLastVars {N : Type w} [L.Structure N] :
    ∀ (m : ℕ) (φ : L.Formulaω (Fin (k + m))) (v : Fin k → N),
      (existsLastVars m φ).Realize v ↔ ∃ ys : Fin m → N, φ.Realize (Fin.append v ys)
  | 0, φ, v => by
    have h : Fin.append v (Fin.elim0 : Fin 0 → N) = v := funext fun i ↦ Fin.append_left v _ i
    rw [existsLastVars_zero]
    refine ⟨fun hφ ↦ ⟨Fin.elim0, by rwa [h]⟩, fun ⟨ys, hφ⟩ ↦ ?_⟩
    rwa [Subsingleton.elim ys Fin.elim0, h] at hφ
  | m + 1, φ, v => by
    rw [existsLastVars_succ, realize_existsLastVars m]
    simp only [realize_existsLastVar]
    refine ⟨fun ⟨ys, x, hφ⟩ ↦ ⟨Fin.snoc ys x, by rwa [Fin.append_snoc]⟩, fun ⟨zs, hφ⟩ ↦
      ⟨Fin.init zs, zs (Fin.last m), by rwa [← Fin.append_snoc, Fin.snoc_init_self]⟩⟩

/-- **Rank of the existential closure**: closing `m` variables adds exactly `m`.  A candidate for
upstreaming to InfinitaryLogic, beside `qrank_existsLastVar`. -/
theorem qrank_existsLastVars :
    ∀ (m : ℕ) (φ : L.Formulaω (Fin (k + m))), (existsLastVars m φ).qrank = φ.qrank + m
  | 0, φ => by simp
  | m + 1, φ => by
    rw [existsLastVars_succ, qrank_existsLastVars m]
    simp only [existsLastVar, Formulaω.qrank, qrank_ex, qrank_relabel]
    rw [add_assoc]
    exact congrArg _ (by exact_mod_cast Nat.add_comm 1 m)

/-! ### The extension formula -/

/-- The equations `z_{f i} = x_i` for `i < k`, in the variables `x̄` (the first `k`) and `z̄`
(the last `m`): a finite conjunction of equations. -/
def extensionEquations (f : Fin k → Fin m) : L.Formulaω (Fin (k + m)) :=
  einf fun i : Fin k ↦ equal (Term.var (Sum.inl (Fin.natAdd k (f i))))
    (Term.var (Sum.inl (Fin.castAdd m i)))

/-- The equations hold of `x̄` followed by `z̄` exactly when `z̄ ∘ f = x̄`. -/
theorem realize_extensionEquations {N : Type w} [L.Structure N] (f : Fin k → Fin m)
    (v : Fin k → N) (s : Fin m → N) :
    (extensionEquations (L := L) f).Realize (Fin.append v s) ↔ s ∘ f = v := by
  simp only [extensionEquations, Formulaω.realize_def, BoundedFormulaω.realize_einf,
    realize_equal, Term.realize_var, Sum.elim_inl, Fin.append_left, Fin.append_right, funext_iff,
    Function.comp_apply]

/-- The equations have quantifier rank `0`. -/
@[simp]
theorem qrank_extensionEquations (f : Fin k → Fin m) :
    (extensionEquations (L := L) f).qrank = 0 := by
  simp only [extensionEquations, Formulaω.qrank, qrank_einf, qrank_equal, Ordinal.iSup_eq_zero_iff,
    implies_true]

/-- The **extension formula** of `ψ` along `f : Fin k → Fin m`: `∃ z̄ (ψ(z̄) ∧ ⋀_{i<k} z_{f i} =
x_i)`, in the free variables `x̄ = x_0, …, x_{k-1}`.  A candidate for upstreaming to
InfinitaryLogic. -/
def extendFormula (ψ : L.Formulaω (Fin m)) (f : Fin k → Fin m) : L.Formulaω (Fin k) :=
  existsLastVars m (BoundedFormulaω.mapFreeVars (Fin.natAdd k) ψ ⊓ extensionEquations f)

/-- **Semantics of the extension formula**: it holds of `c` exactly when `c` extends along `f` to a
tuple realizing `ψ`.  A candidate for upstreaming to InfinitaryLogic. -/
theorem realize_extendFormula {N : Type w} [L.Structure N] (ψ : L.Formulaω (Fin m))
    (f : Fin k → Fin m) (c : Fin k → N) :
    (extendFormula ψ f).Realize c ↔ ∃ s : Fin m → N, s ∘ f = c ∧ ψ.Realize s := by
  rw [extendFormula, realize_existsLastVars]
  refine exists_congr fun s ↦ ?_
  rw [Formulaω.realize_inf, realize_extensionEquations, and_comm]
  refine and_congr_right fun _ ↦ ?_
  rw [Formulaω.realize_def, realize_mapFreeVars]
  exact Iff.of_eq (congrArg (BoundedFormulaω.Realize ψ · _) (funext (Fin.append_right c s)))

/-- **Rank of the extension formula**: the rank of `ψ` plus `m`.  A candidate for upstreaming to
InfinitaryLogic. -/
theorem qrank_extendFormula (ψ : L.Formulaω (Fin m)) (f : Fin k → Fin m) :
    (extendFormula ψ f).qrank = ψ.qrank + m := by
  rw [extendFormula, qrank_existsLastVars]
  refine congrArg (· + (m : Ordinal)) ((qrank_inf _ _).trans ?_)
  rw [qrank_mapFreeVars]
  exact max_eq_left ((qrank_extensionEquations f).trans_le zero_le)

end FirstOrder.Language

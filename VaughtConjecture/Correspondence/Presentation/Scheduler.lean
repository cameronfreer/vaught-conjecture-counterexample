/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Construction.DenseChain
import VaughtConjecture.Correspondence.Presentation.Alignment
import VaughtConjecture.Extension.StronglyCodedAmalgamation
import VaughtConjecture.Stage.Countable

/-!
# Presentation: a positional realization with a given class reading

Native construction throughout.  Write `λ_β = blockStage β`.

**Theorem** (`ClassRealization.exists_realization_classReading_eq`).  At a stage `α` that is zero
or a limit with countably many ordinals below it, on a countable carrier, a well-formed class
realization with donor density is the class reading of an exactly consistent, covering realization
with strongly coded legal types and finite-extension receiving for the strongly coded legal donors.
Hence the target B.T7 holds (`presentationTarget`); its premise `Nonempty M` is not used.

**The construction** (a countable scheduler, by the Rasiowa–Sikorski lemma
`Construction.exists_monotone_forall_exists_mem`).

* **Conditions** (`ClassRealization.Condition`): a tuple `W` typed in `S` with a stage type `w` of
  its class.  `c ≤ d` when the tuple of `c` is a face of the tuple of `d` along some `e` and
  `restrictFace e d.w = some c.w` literally.  The positional type of every tuple whose points are
  points of `W` is its face of `w`; faces agree along extensions
  (`Condition.restrictFace_eq_of_le`).
* **Points** (`exists_le_mem_range`): covering gives a typed tuple containing the points of `W`
  and any finitely many further points; a representative of its class has `w` as its literal face
  (`TemplateClass.exists_renaming_restrictFace_eq`).
* **Receiving tasks** (`exists_le_taskDone`): for a root `t`, a strongly coded legal donor `D`
  with face `p` (the type of `t`) along `g`, and a permitted cutoff `x`:
  1. amalgamate `D` with `w` over `p` (`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit`):
     a strongly coded legal `D⁺` with faces `D` along `i` and `w` along `j`;
  2. choose a permitted cutoff `x' ≥ x` above every label of `w` other than the formal top
     (`StageType.exists_isPermittedCutoff_above`);
  3. apply **donor density** of `S` at the tuple `W` to the class of `D⁺` along `j` at `x'`: a
     tuple `U` with `j.trans U = W` whose class has a representative `q'` in the receiving family
     of `D⁺` at `x'`;
  4. the face of `q'` along `j` is a renaming of `w` agreeing with `w` below `x'`, hence `w`
     itself (`StageType.eq_of_mem_receivingFamily`); so `(U, q')` extends the condition, and the
     face of `q'` along `i` is in the receiving family of `D` at `x'`, hence at `x`.
* **Countably many requirements**: a point of `M`, or a task indexed by a root, a donor, an
  embedding and a permitted cutoff; countable since `M` is, and there are countably many stage
  types and labels at `α` (`StageType.countable`, `Label.countable_setOf_atStage`).

**What the construction uses of the class realization**: consistency and covering (for the
conditions and points), legal types (strong coding and legality of `w`, for the amalgamation), and
donor density at strongly coded legal donors on the tuples of conditions, at cutoffs above the
labels of the root (for the tasks).  Root alignment at a cutoff above the root's labels is what
turns density up to renaming into literal receiving: below such a cutoff a renaming of the root
type that agrees with it is the identity on labels.
-/

universe u v

namespace VaughtConjecture

open Finset

noncomputable section

/-! ### A cutoff above the labels of a type, and rigidity at such a cutoff -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **A permitted cutoff above the proper labels of a type**: at a stage that is zero or a limit,
above a permitted cutoff `c` there is a permitted cutoff `x` such that every label of `w` is below
`x` or the formal top.  Native construction. -/
theorem exists_isPermittedCutoff_above (hα : Order.IsSuccPrelimit α) {c : Label.{u}}
    (hc : Label.IsPermittedCutoff α c) (w : StageType.{u} α n) :
    ∃ x : Label.{u}, Label.IsPermittedCutoff α x ∧ c ≤ x ∧
      ∀ d, w.label d < x ∨ w.label d = ⊤ := by
  classical
  let F : Fin w.card → Label.{u} := fun d ↦ if w.label d = ⊤ then ⊥ else w.label d
  let s : Label.{u} := Finset.univ.sup F ⊔ c
  have hF (d : Fin w.card) : F d < α := by
    by_cases hd : w.label d = ⊤
    · simp only [F, hd, ite_true]
      exact hc.1.trans hc.2
    · simp only [F, hd, ite_false]
      exact (w.atStage d).resolve_right hd
  have hs : s < α := sup_lt_iff.mpr ⟨(Finset.sup_lt_iff (hc.1.trans hc.2)).mpr fun d _ ↦ hF d, hc.2⟩
  have hcs : c ≤ s := le_sup_right
  obtain ⟨o, ho, hos⟩ : ∃ o < α, (o : Label.{u}) = s := by
    rcases Label.atStage_iff.mp (Or.inl hs : Label.AtStage α s) with h | h | h
    · exact absurd (h ▸ hc.1.trans_le hcs) (lt_irrefl _)
    · exact h
    · exact absurd (h ▸ hs) (not_lt.mpr le_top)
  have hso : o < Order.succ o := Order.lt_succ o
  have hlt : ((o : Label.{u})) < ((Order.succ o : Ordinal.{u}) : Label.{u}) := by
    exact_mod_cast hso
  refine ⟨(Order.succ o : Ordinal.{u}), ?_, hcs.trans (hos ▸ hlt.le), fun d ↦ ?_⟩
  · exact Label.isPermittedCutoff_coe.mpr (hα.succ_lt ho)
  · by_cases hd : w.label d = ⊤
    · exact .inr hd
    · refine .inl (lt_of_le_of_lt ?_ (hos ▸ hlt))
      have : F d ≤ s := le_sup_of_le_left (Finset.le_sup (f := F) (Finset.mem_univ d))
      simpa only [F, hd, ite_false] using this

/-- **Rigidity at a cutoff above the proper labels**: a renaming `a` of `b` in the receiving
family of `b` at a cutoff `x` above every label of `b` other than the formal top is `b`.
Native construction. -/
theorem eq_of_mem_receivingFamily {a b : StageType.{u} α n} {x : Label.{u}}
    (ha : a ∈ receivingFamily b x) (hab : b.IsCellRenaming a)
    (hb : ∀ d, b.label d < x ∨ b.label d = ⊤) : a = b := by
  obtain ⟨k, σ, rfl⟩ := hab
  refine StageType.ext ha.1 fun i j hij ↦ ?_
  have hm : min (b.label (σ i)) x = min (b.label j) x := ha.2 i j hij
  change b.label (σ i) = b.label j
  rcases hb j with hj | hj
  · rw [min_eq_left hj.le] at hm
    rcases le_or_gt x (b.label (σ i)) with h | h
    · rw [min_eq_right h] at hm
      exact absurd hm.symm hj.ne
    · rwa [min_eq_left h.le] at hm
  · rw [hj, min_eq_right le_top] at hm
    rcases hb (σ i) with h | h
    · rw [min_eq_left h.le] at hm
      exact absurd hm h.ne
    · rw [h, hj]

end StageType

/-! ### Conditions -/

namespace ClassRealization

open StageType

variable {α : Ordinal.{u}} {M : Type v} (S : ClassRealization.{u, v} α M)

/-- **A condition** of the construction of a presentation of `S` (native construction): a tuple
`W` typed in `S`, with a stage type `w` of its class.  The positional types of all tuples whose
points are points of `W` are the faces of `w`. -/
structure Condition where
  /-- The number of points. -/
  N : ℕ
  /-- The tuple. -/
  W : Fin N ↪ M
  /-- The positional type of the tuple. -/
  w : StageType.{u} α N
  /-- The type is a representative of the class of the tuple. -/
  eval_W : S.eval W = some w.toClass

namespace Condition

variable {S}

/-- A condition `d` **extends** `c` when the tuple of `c` is a face of the tuple of `d` along some
`e`, and the type of `c` is literally the face of the type of `d` along `e`.  Native construction.
-/
instance : Preorder S.Condition where
  le c d := ∃ e : Fin c.N ↪ Fin d.N, e.trans d.W = c.W ∧ restrictFace e d.w = some c.w
  le_refl c := ⟨Function.Embedding.refl _, rfl, restrictFace_refl c.w⟩
  le_trans c d d' := by
    rintro ⟨e, he, hew⟩ ⟨e', he', hew'⟩
    refine ⟨e.trans e', ?_, ?_⟩
    · rw [← he, ← he']
      rfl
    · rw [← restrictFace_trans d'.w e' e hew', hew]

theorem le_def {c d : S.Condition} :
    c ≤ d ↔ ∃ e : Fin c.N ↪ Fin d.N, e.trans d.W = c.W ∧ restrictFace e d.w = some c.w :=
  Iff.rfl

/-- Along an extension, the tuple of a condition has its points among those of the extension. -/
theorem range_subset_of_le {c d : S.Condition} (h : c ≤ d) :
    Set.range c.W ⊆ Set.range d.W := by
  obtain ⟨e, he, -⟩ := h
  rintro _ ⟨j, rfl⟩
  exact ⟨e j, by rw [← he]; rfl⟩

/-- **Faces agree along an extension**: a tuple that is a face of the tuples of `c ≤ d` along `h`
and `h'` has the same face of the two types.  Native construction. -/
theorem restrictFace_eq_of_le {c d : S.Condition} (hcd : c ≤ d) {k : ℕ} {t : Fin k ↪ M}
    {h : Fin k ↪ Fin c.N} {h' : Fin k ↪ Fin d.N} (hh : h.trans c.W = t)
    (hh' : h'.trans d.W = t) : restrictFace h c.w = restrictFace h' d.w := by
  obtain ⟨e, he, hew⟩ := hcd
  have : h' = h.trans e := Function.Embedding.ext fun j ↦ d.W.injective <| by
    have h1 := DFunLike.congr_fun hh' j
    have h2 := DFunLike.congr_fun hh j
    have h3 := DFunLike.congr_fun he (h j)
    simp only [Function.Embedding.trans_apply] at h1 h2 h3 ⊢
    rw [h1, ← h2, ← h3]
  rw [this, restrictFace_trans d.w e h hew]

end Condition

variable {S}

/-- **Extension to a typed tuple containing the tuple of a condition**: if the tuple of `c` is
the face along `e` of a tuple `U` typed in `S`, some stage type of the class of `U` has the type
of `c` as its face along `e` (`TemplateClass.exists_renaming_restrictFace_eq`).
Native construction. -/
theorem exists_le_of_trans_eq (hS : S.IsConsistent) (c : S.Condition) {N : ℕ} {U : Fin N ↪ M}
    (hU : (S.eval U).isSome) (e : Fin c.N ↪ Fin N) (he : e.trans U = c.W) :
    ∃ (u : StageType.{u} α N) (hu : S.eval U = some u.toClass), c ≤ ⟨N, U, u, hu⟩ := by
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hU
  induction Q using Quotient.inductionOn with
  | h q =>
    have hface : q.toClass.restrictFace e = some c.w.toClass := by
      rw [← hS U _ e hQ, he, c.eval_W]
    obtain ⟨u, hu, hue⟩ := TemplateClass.exists_renaming_restrictFace_eq q e hface
    exact ⟨u, hQ.trans (congrArg some hu.symm), e, he, hue⟩

/-- **Extension to a condition containing finitely many given points** (covering).
Native construction. -/
theorem exists_le_mem_range (hS : S.IsWellFormed) (c : S.Condition) (A : Finset M) :
    ∃ d : S.Condition, c ≤ d ∧ ∀ x ∈ A, x ∈ Set.range d.W := by
  classical
  let B : Finset M := A ∪ Finset.univ.image c.W
  let b : Fin B.card ↪ M := B.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨N, U, g, hgU, hU⟩ := hS.isCovering b
  have hB (x : M) (hx : x ∈ B) : x ∈ Set.range U := by
    refine ⟨g (B.equivFin ⟨x, hx⟩), ?_⟩
    have := DFunLike.congr_fun hgU (B.equivFin ⟨x, hx⟩)
    simpa [b] using this
  obtain ⟨e, he⟩ := Realization.exists_trans_eq_of_forall_mem_range (w := U) (t := c.W)
    fun j ↦ hB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  obtain ⟨u, hu, hcu⟩ := exists_le_of_trans_eq hS.isConsistent c hU e he
  exact ⟨_, hcu, fun x hx ↦ hB x (Finset.mem_union_left _ hx)⟩

/-! ### Receiving tasks -/

/-- **A receiving task done at a condition** (native construction): the root `t` is a face of the
tuple of `c` along some `h`, and if its type `p` (the face of the type of `c` along `h`) is the
face along `g` of a strongly coded legal donor `D`, and `x` is a permitted cutoff, then some face
`i.trans c.W` of the tuple of `c` extends `t` along `g` and has a type in the receiving family of
`D` at `x`. -/
def Condition.TaskDone (c : S.Condition) {k m : ℕ} (t : Fin k ↪ M) (D : StageType.{u} α m)
    (g : Fin k ↪ Fin m) (x : Label.{u}) : Prop :=
  ∃ h : Fin k ↪ Fin c.N, h.trans c.W = t ∧ ∀ p, restrictFace h c.w = some p →
    D.IsStronglyCodedLegal → restrictFace g D = some p → Label.IsPermittedCutoff α x →
      ∃ i : Fin m ↪ Fin c.N, g.trans (i.trans c.W) = t ∧
        ∃ q ∈ receivingFamily D x, restrictFace i c.w = some q

/-- **Every receiving task can be done** (native construction), at a stage that is zero or a
limit, for a well-formed class realization with donor density.  Extend `c` to contain the points
of `t`; amalgamate the donor `D` with the type `w` of the condition over the root
(`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit`), giving a strongly coded legal `D⁺`
with faces `D` along `i` and `w` along `j`; choose a permitted cutoff `x'` at least `x` and above
every label of `w` other than the formal top (`StageType.exists_isPermittedCutoff_above`); apply
donor density at the tuple of the condition to the class of `D⁺` along `j` at `x'`.  The received
tuple `U` has a representative `q'` of its class in the receiving family of `D⁺` at `x'`; its face
along `j` is a renaming of `w` agreeing with `w` below `x'`, hence `w` itself
(`StageType.eq_of_mem_receivingFamily`), and its face along `i` is in the receiving family of `D`
at `x'`, hence at `x`. -/
theorem exists_le_taskDone (hS : S.IsWellFormed) (hden : S.HasDonorDensity)
    (hα : Order.IsSuccPrelimit α) (c : S.Condition) {k m : ℕ} (t : Fin k ↪ M)
    (D : StageType.{u} α m) (g : Fin k ↪ Fin m) (x : Label.{u}) :
    ∃ d : S.Condition, c ≤ d ∧ d.TaskDone t D g x := by
  classical
  obtain ⟨d₁, hcd₁, hd₁⟩ := exists_le_mem_range hS c (Finset.univ.image t)
  obtain ⟨h, hh⟩ := Realization.exists_trans_eq_of_forall_mem_range (w := d₁.W) (t := t)
    fun j ↦ hd₁ _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  by_cases H : ∃ p, restrictFace h d₁.w = some p ∧ D.IsStronglyCodedLegal ∧
      restrictFace g D = some p ∧ Label.IsPermittedCutoff α x
  swap
  · exact ⟨d₁, hcd₁, h, hh, fun p hp hD hg hx ↦ absurd ⟨p, hp, hD, hg, hx⟩ H⟩
  obtain ⟨p, hp, hD, hg, hx⟩ := H
  have hw : d₁.w.IsStronglyCodedLegal := hS.hasLegalTypes _ _ d₁.eval_W
  obtain ⟨N, Dp, i, j, hDp, hi, hj, hij⟩ :=
    exists_stronglyCoded_amalgam_of_isSuccPrelimit hα hD hw hg hp
  obtain ⟨x', hx', hxx', hlab⟩ := exists_isPermittedCutoff_above hα hx d₁.w
  obtain ⟨U, hjU, Q, hQ, hobs⟩ := hden d₁.W d₁.w.toClass d₁.eval_W Dp.toClass j hDp
    (by rw [TemplateClass.restrictFace_toClass, hj, Option.map_some]) x' hx'
  induction Q using Quotient.inductionOn with
  | h q₀ =>
  obtain ⟨q', hq₀q', hq'⟩ := TemplateClass.observesAt_toClass_iff.mp hobs
  have hQ' : S.eval U = some q'.toClass :=
    hQ.trans (congrArg some (toClass_eq_toClass_iff.mpr hq₀q'))
  obtain ⟨w'', hw''j, hw''⟩ := exists_restrictFace_mem_receivingFamily hq' hj
  have hclass : d₁.w.toClass = w''.toClass := by
    have := hS.isConsistent U q'.toClass j hQ'
    rw [hjU, d₁.eval_W, TemplateClass.restrictFace_toClass, hw''j, Option.map_some] at this
    exact Option.some.inj this
  obtain rfl : w'' = d₁.w :=
    eq_of_mem_receivingFamily hw'' (toClass_eq_toClass_iff.mp hclass) hlab
  obtain ⟨Di, hDi, hDi'⟩ := exists_restrictFace_mem_receivingFamily hq' hi
  refine ⟨⟨N, U, q', hQ'⟩, hcd₁.trans ⟨j, hjU, hw''j⟩, h.trans j, ?_, fun _ _ _ _ _ ↦
    ⟨i, ?_, Di, mem_receivingFamily_of_le hDi' hxx', hDi⟩⟩
  · rw [← hh, ← hjU]
    rfl
  · refine Function.Embedding.ext fun a ↦ ?_
    have h1 := DFunLike.congr_fun hij a
    have h2 := DFunLike.congr_fun hjU (h a)
    have h3 := DFunLike.congr_fun hh a
    simp only [Function.Embedding.trans_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]

/-! ### The construction -/

/-- **A positional presentation of a dense class realization** (native construction).  At a stage
`α` that is zero or a limit with countably many ordinals below it, on a countable carrier, every
well-formed class realization `S` with donor density is the class reading of an exactly
consistent, covering realization with strongly coded legal types and finite-extension receiving
for the strongly coded legal donors.

Proof: the conditions (`ClassRealization.Condition`, a typed tuple with a representative of its
class, extended along literal faces) and countably many dense sets of conditions: containing a
point of `M` (`exists_le_mem_range`, from covering) and doing a receiving task
(`exists_le_taskDone`, from donor density and strongly coded amalgamation).  The tasks are indexed
by a root, a donor, an embedding and a permitted cutoff, countably many since `M` is countable and
there are countably many stage types at `α` (`StageType.countable`) and countably many labels at
`α`.  A chain meeting every dense set (`Construction.exists_monotone_forall_exists_mem`) gives
the realization: the type of a tuple is its face of the type of any condition of the chain whose
tuple contains its points (`Condition.restrictFace_eq_of_le`). -/
theorem exists_realization_classReading_eq [Countable M] (hα : Order.IsSuccPrelimit α)
    (hcount : (Set.Iio α).Countable) (hS : S.IsWellFormed) (hden : S.HasDonorDensity) :
    ∃ R : Realization.{u, v} α M, R.IsConsistent ∧ R.IsCovering ∧
      (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
        p.IsStronglyCodedLegal) ∧
      R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) ∧ R.classReading = S := by
  classical
  -- the initial condition: the empty tuple
  let W₀ : Fin 0 ↪ M := Function.Embedding.ofIsEmpty
  let c₀ : S.Condition := ⟨0, W₀, Quotient.out (TemplateClass.empty α), by
    rw [eval_zero hS.isConsistent hS.isCovering W₀]
    exact congrArg some (Quotient.out_eq _).symm⟩
  -- the countably many requirements
  have : ∀ k, Countable (Fin k ↪ M) := fun k ↦
    Function.Injective.countable (f := fun e : Fin k ↪ M ↦ (e : Fin k → M)) DFunLike.coe_injective
  have := StageType.countable hcount
  have : Countable {x : Label.{u} // Label.IsPermittedCutoff α x} :=
    ((Label.countable_setOf_atStage hcount).mono (s₁ := {x | Label.IsPermittedCutoff α x})
      fun _ hx ↦ Or.inl hx.2).to_subtype
  let ι := M ⊕ Σ (k m : ℕ), (Fin k ↪ M) × StageType.{u} α m × (Fin k ↪ Fin m) ×
    {x : Label.{u} // Label.IsPermittedCutoff α x}
  let Dense : ι → Set S.Condition := fun i ↦ match i with
    | .inl a => {c | a ∈ Set.range c.W}
    | .inr ⟨_, _, t, D, g, x⟩ => {c | c.TaskDone t D g x.1}
  have hDense : ∀ i c, c₀ ≤ c → ∃ d ∈ Dense i, c ≤ d := by
    rintro (a | ⟨k, m, t, D, g, x⟩) c -
    · obtain ⟨d, hcd, hd⟩ := exists_le_mem_range hS c {a}
      exact ⟨d, hd a (Finset.mem_singleton_self a), hcd⟩
    · obtain ⟨d, hcd, hd⟩ := exists_le_taskDone hS hden hα c t D g x.1
      exact ⟨d, hd, hcd⟩
  obtain ⟨cs, -, hmono, hmeet⟩ := Construction.exists_monotone_forall_exists_mem c₀ Dense hDense
  -- every tuple is a face of the tuple of some condition of the chain
  have hpt (a : M) : ∃ n, a ∈ Set.range (cs n).W := hmeet (.inl a)
  have hface {k : ℕ} (t : Fin k ↪ M) : ∃ n, ∃ h : Fin k ↪ Fin (cs n).N, h.trans (cs n).W = t := by
    choose nf hnf using fun j : Fin k ↦ hpt (t j)
    let n := Finset.univ.sup nf
    refine ⟨n, Realization.exists_trans_eq_of_forall_mem_range fun j ↦ ?_⟩
    exact Condition.range_subset_of_le (hmono (Finset.le_sup (Finset.mem_univ j))) (hnf j)
  -- faces along different conditions agree
  have hwd {k : ℕ} {t : Fin k ↪ M} {n n' : ℕ} {h : Fin k ↪ Fin (cs n).N}
      {h' : Fin k ↪ Fin (cs n').N} (hh : h.trans (cs n).W = t) (hh' : h'.trans (cs n').W = t) :
      restrictFace h (cs n).w = restrictFace h' (cs n').w := by
    rcases le_total n n' with hnn | hnn
    · exact Condition.restrictFace_eq_of_le (hmono hnn) hh hh'
    · exact (Condition.restrictFace_eq_of_le (hmono hnn) hh' hh).symm
  let R : Realization.{u, v} α M :=
    ⟨fun t ↦ restrictFace (hface t).choose_spec.choose (cs (hface t).choose).w⟩
  have hR {k : ℕ} {t : Fin k ↪ M} {n : ℕ} {h : Fin k ↪ Fin (cs n).N}
      (hh : h.trans (cs n).W = t) : R.eval t = restrictFace h (cs n).w :=
    hwd (hface t).choose_spec.choose_spec hh
  have hread : R.classReading = S := by
    refine ClassRealization.ext fun t ↦ ?_
    obtain ⟨n, h, hh⟩ := hface t
    rw [Realization.classReading_eval, hR hh, ← TemplateClass.restrictFace_toClass,
      ← hS.isConsistent _ _ h (cs n).eval_W, hh]
  refine ⟨R, ?_, ?_, ?_, ?_, hread⟩
  · -- exact consistency
    intro m k t p f hp
    obtain ⟨n, h, hh⟩ := hface t
    rw [hR hh] at hp
    rw [hR (h := f.trans h) (by rw [← hh]; rfl), restrictFace_trans (cs n).w h f hp]
  · -- covering
    intro k t
    obtain ⟨n, h, hh⟩ := hface t
    refine ⟨_, (cs n).W, h, hh, ?_⟩
    rw [hR (t := (cs n).W) (h := Function.Embedding.refl _) rfl, restrictFace_refl]
    rfl
  · -- strongly coded legal types
    intro k t p hp
    have : S.eval t = some p.toClass := by
      rw [← hread, Realization.classReading_eval, hp, Option.map_some]
    exact hS.hasLegalTypes t _ this
  · -- receiving for the strongly coded legal donors
    intro k m t p hp D g hDl hDs hg x hx
    obtain ⟨n, hn⟩ := hmeet (.inr ⟨k, m, t, D, g, ⟨x, hx⟩⟩)
    obtain ⟨h, hh, hdone⟩ := hn
    obtain ⟨i, hi, q, hq, hiq⟩ := hdone p ((hR hh).symm.trans hp) ⟨hDl, hDs⟩ hg hx
    exact ⟨i.trans (cs n).W, hi, q, hq, (hR rfl).trans hiq⟩

end ClassRealization

/-! ### The presentation target -/

/-- **Target B.T7, presentation, holds** (native construction): `PresentationTarget β M` for every
`β` and `M`.  Used: `β < ω₁` (countably many ordinals below `λ_β`), countability of `M`, and the
well-formedness and donor density of the class realization; the stage `λ_β` is a limit.  The
premise `Nonempty M` is not used. -/
theorem presentationTarget (β : Ordinal.{u}) (M : Type v) : PresentationTarget β M :=
  fun hβ hM _ S hS hden ↦
    haveI := hM
    S.exists_realization_classReading_eq (isSuccPrelimit_blockStage β)
      (Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)) hS hden

end

end VaughtConjecture

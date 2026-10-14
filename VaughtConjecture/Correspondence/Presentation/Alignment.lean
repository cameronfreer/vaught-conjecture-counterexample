/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Compactness.Compact
import VaughtConjecture.Correspondence.Presentation.Targets

/-!
# Alignment: equal class readings give a coherent renaming

Native construction throughout.

**Theorem** (`Realization.exists_coherentRenaming`).  For exactly consistent realizations `R`,
`R'` at the same stage on the same carrier, with `R` covering, equal class readings give a
coherent renaming of `R` into `R'` (`Realization.CoherentRenaming`).  Hence the targets B.T8
(`alignmentTarget`) and reduction alignment (`reductionAlignmentTarget`) hold; their remaining
premises (`β < ω₁`, countability, strongly coded legal types, receiving) are not used.

**Proof.**

* **Faces of renamings** (`StageType.Renaming.exists_face`, `StageType.Renaming.face`): if `p` is
  a renaming of `q`, the faces of `p` and `q` along `g` are related by a renaming whose bijection
  commutes with the face cell maps.  Face cell maps compose (`StageType.faceCellMap_trans`).
* **Local coherence** (`Realization.isCoherentAt_inducedChoices`): a renaming at one typed tuple
  `w` induces, at every face of `w`, the face renaming; these commute with the face cell maps at
  every face of a face of `w`.
* **Compactness.**  The choices of a renaming at every tuple typed in both
  (`Realization.Choices`, a product of finite discrete spaces, compact by Tychonoff) satisfying
  coherence at a given tuple and face form a closed set
  (`Realization.isClosed_setOf_isCoherentAt`).  Finitely many tuples have their points in one
  typed tuple `w` (covering), so finitely many conditions hold for the choices induced by `w`; by
  compactness all hold at once (`IsCompact.inter_iInter_nonempty`), and the choices form a
  coherent renaming (`Realization.CoherentRenaming.ofChoices`).
-/

universe u v

namespace VaughtConjecture

open Finset

noncomputable section

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### Faces of faces -/

/-- **Face cell maps compose**: the face cell map of a face of a face is the composite of the two
face cell maps.  Native construction. -/
theorem faceCellMap_trans {p : StageType.{u} α n} {p₀ : StageType.{u} α m}
    {p₀₀ : StageType.{u} α k} {g : Fin m ↪ Fin n} {f : Fin k ↪ Fin m}
    (hp : restrictFace g p = some p₀) (hp₀ : restrictFace f p₀ = some p₀₀) (i : Fin p₀₀.card) :
    faceCellMap ((restrictFace_trans p g f hp).symm.trans hp₀) i =
      faceCellMap hp (faceCellMap hp₀ i) := by
  obtain ⟨hg, rfl⟩ := (restrictFace_eq_some_iff p g).mp hp
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ f).mp hp₀
  exact (p.toScheme.cellMap_cellMap g f rfl).symm

/-- The cells named by a face are the cells visible through it.  Native construction. -/
theorem mem_range_faceCellMap {p : StageType.{u} α n} {p₀ : StageType.{u} α m}
    {g : Fin m ↪ Fin n} (h : restrictFace g p = some p₀) (d : Fin p.card) :
    d ∈ Set.range (faceCellMap h) ↔ d ∈ p.visibleCells g := by
  constructor
  · rintro ⟨i, rfl⟩
    exact p.cellMap_mem g _
  · intro hd
    have hd' : d ∈ Set.range (p.cellMap g) := by
      rw [Scheme.range_cellMap]
      exact hd
    obtain ⟨x, rfl⟩ := hd'
    exact ⟨Fin.cast (card_eq_of_restrictFace_eq_some h).symm x, rfl⟩

namespace Renaming

variable {p q : StageType.{u} α n} {p₀ q₀ : StageType.{u} α m} {g : Fin m ↪ Fin n}

/-- Renamings with the same bijection are equal.  Native construction. -/
theorem ext_toEquiv {r r' : p.Renaming q} (h : r.toEquiv = r'.toEquiv) : r = r' := by
  obtain ⟨e, he⟩ := r
  obtain ⟨e', he'⟩ := r'
  subst h
  rfl

instance : Finite (p.Renaming q) :=
  Finite.of_injective toEquiv fun _ _ h ↦ ext_toEquiv h

/-- A renaming of a face, read through the face cell maps. -/
private theorem renameCells_face_eq {k : ℕ} (σ : Fin k ≃ Fin q.card) (p : StageType.{u} α n)
    (h : q.renameCells σ = p) (hp : restrictFace g p = some p₀)
    (hq : restrictFace g q = some q₀) (τ : Fin p₀.card ≃ Fin q₀.card)
    (hτ : ∀ i (c : Fin k), (c : ℕ) = faceCellMap hp i → faceCellMap hq (τ i) = σ c) :
    q₀.renameCells τ = p₀ := by
  subst h
  obtain ⟨hf', rfl⟩ := (restrictFace_eq_some_iff _ g).mp hp
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff q g).mp hq
  exact comap_renameCells_eq q σ g hf τ fun j ↦ hτ j _ rfl

/-- **The face of a renaming** (native construction): if `p` is the renaming of `q` along `σ`, the
faces `p₀`, `q₀` along `g` are related by a renaming whose bijection commutes with the face cell
maps: `faceCellMap hq ∘ σ₀ = σ ∘ faceCellMap hp`. -/
theorem exists_face (r : q.Renaming p) (hp : restrictFace g p = some p₀)
    (hq : restrictFace g q = some q₀) :
    ∃ r₀ : q₀.Renaming p₀, ∀ i, faceCellMap hq (r₀.toEquiv i) = r.toEquiv (faceCellMap hp i) := by
  have hvis (i : Fin p₀.card) : r.toEquiv (faceCellMap hp i) ∈ Set.range (faceCellMap hq) := by
    rw [mem_range_faceCellMap, Scheme.mem_visibleCells, ← r.scope_eq]
    exact Scheme.mem_visibleCells.mp ((mem_range_faceCellMap hp _).mp ⟨i, rfl⟩)
  let F : Fin p₀.card → Fin q₀.card := fun i ↦ (hvis i).choose
  have hF (i : Fin p₀.card) : faceCellMap hq (F i) = r.toEquiv (faceCellMap hp i) :=
    (hvis i).choose_spec
  have hinj : Function.Injective F := fun i j hij ↦ by
    have := congrArg (faceCellMap hq) hij
    rw [hF, hF] at this
    exact faceCellMap_injective hp (r.toEquiv.injective this)
  have hcard : p₀.card = q₀.card := by
    obtain ⟨s', hs', hss'⟩ := restrictFace_renameCells q r.toEquiv g hq
    rw [r.renameCells_eq, hp] at hs'
    obtain rfl := Option.some.inj hs'
    exact hss'.card_eq
  let τ : Fin p₀.card ≃ Fin q₀.card :=
    Equiv.ofBijective F ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, by simp [hcard]⟩)
  refine ⟨⟨τ, renameCells_face_eq r.toEquiv p r.renameCells_eq hp hq τ fun i c hc ↦ ?_⟩, hF⟩
  rw [Fin.ext hc]
  exact hF i

/-- **The face of a renaming**, chosen (`exists_face`).  Native construction. -/
def face (r : q.Renaming p) (hp : restrictFace g p = some p₀) (hq : restrictFace g q = some q₀) :
    q₀.Renaming p₀ :=
  (r.exists_face hp hq).choose

/-- The face of a renaming commutes with the face cell maps.  Native construction. -/
theorem faceCellMap_face (r : q.Renaming p) (hp : restrictFace g p = some p₀)
    (hq : restrictFace g q = some q₀) (i : Fin p₀.card) :
    faceCellMap hq ((r.face hp hq).toEquiv i) = r.toEquiv (faceCellMap hp i) :=
  (r.exists_face hp hq).choose_spec i

end Renaming

/-! ### Optional renamings -/

/-- **A renaming at a pair of optional types**: a renaming of `q` to `p` when the types are
`some p` and `some q`, and nothing otherwise.  Native construction. -/
def RenamingOpt : Option (StageType.{u} α n) → Option (StageType.{u} α n) → Type
  | some p, some q => q.Renaming p
  | _, _ => PUnit

namespace RenamingOpt

instance instFinite (a b : Option (StageType.{u} α n)) : Finite (RenamingOpt a b) := by
  cases a with
  | none => exact (inferInstance : Finite PUnit.{1})
  | some p =>
    cases b with
    | none => exact (inferInstance : Finite PUnit.{1})
    | some q => exact (inferInstance : Finite (q.Renaming p))

instance instTopologicalSpace (a b : Option (StageType.{u} α n)) :
    TopologicalSpace (RenamingOpt a b) :=
  ⊥

instance instDiscreteTopology (a b : Option (StageType.{u} α n)) :
    DiscreteTopology (RenamingOpt a b) :=
  ⟨rfl⟩

/-- The renaming at `some p`, `some q`.  Native construction. -/
def get {a b : Option (StageType.{u} α n)} (x : RenamingOpt a b) {p q : StageType.{u} α n}
    (ha : a = some p) (hb : b = some q) : q.Renaming p := by
  subst ha hb
  exact x

/-- A renaming at a pair of optional types from renamings at every pair of values.
Native construction. -/
def mk : ∀ {a b : Option (StageType.{u} α n)},
    (∀ p q, a = some p → b = some q → q.Renaming p) → RenamingOpt a b
  | some p, some q, F => F p q rfl rfl
  | none, _, _ => PUnit.unit
  | some _, none, _ => PUnit.unit

@[simp] theorem get_mk {a b : Option (StageType.{u} α n)}
    (F : ∀ p q, a = some p → b = some q → q.Renaming p) {p q : StageType.{u} α n}
    (ha : a = some p) (hb : b = some q) : (mk F).get ha hb = F p q ha hb := by
  subst ha hb
  rfl

end RenamingOpt

end StageType

/-! ### Choices of renamings and their coherence -/

namespace Realization

open StageType

variable {α : Ordinal.{u}} {M : Type v} {R R' : Realization.{u, v} α M} {n m N : ℕ}

variable (R R') in
/-- **Choices of renamings**: a renaming at every tuple typed in both realizations.  With the
discrete topology on each factor, a compact space (Tychonoff).  Native construction. -/
abbrev Choices : Type v :=
  ∀ (n : ℕ) (t : Fin n ↪ M), RenamingOpt (R.eval t) (R'.eval t)

/-- **Coherence of choices at a tuple and a face**: the commutation of
`Realization.CoherentRenaming.faceCellMap_comm` at `t` and `f`.  Native construction. -/
def IsCoherentAt (s : Choices R R') (t : Fin n ↪ M) (f : Fin m ↪ Fin n) : Prop :=
  ∀ ⦃p q : StageType.{u} α n⦄ ⦃p₀ q₀ : StageType.{u} α m⦄ (hp : R.eval t = some p)
    (hq : R'.eval t = some q) (hp₀ : R.eval (f.trans t) = some p₀)
    (hq₀ : R'.eval (f.trans t) = some q₀) (hfp : restrictFace f p = some p₀)
    (hfq : restrictFace f q = some q₀) (i : Fin p₀.card),
    faceCellMap hfq (((s m (f.trans t)).get hp₀ hq₀).toEquiv i) =
      ((s n t).get hp hq).toEquiv (faceCellMap hfp i)

/-- Coherence at a tuple and a face is a closed condition: it reads two coordinates.
Native construction. -/
theorem isClosed_setOf_isCoherentAt (t : Fin n ↪ M) (f : Fin m ↪ Fin n) :
    IsClosed {s : Choices R R' | IsCoherentAt s t f} := by
  let P : RenamingOpt (R.eval t) (R'.eval t) × RenamingOpt (R.eval (f.trans t))
      (R'.eval (f.trans t)) → Prop := fun x ↦
    ∀ ⦃p q : StageType.{u} α n⦄ ⦃p₀ q₀ : StageType.{u} α m⦄ (hp : R.eval t = some p)
      (hq : R'.eval t = some q) (hp₀ : R.eval (f.trans t) = some p₀)
      (hq₀ : R'.eval (f.trans t) = some q₀) (hfp : restrictFace f p = some p₀)
      (hfq : restrictFace f q = some q₀) (i : Fin p₀.card),
      faceCellMap hfq ((x.2.get hp₀ hq₀).toEquiv i) = (x.1.get hp hq).toEquiv (faceCellMap hfp i)
  have hc : Continuous fun s : Choices R R' ↦ (s n t, s m (f.trans t)) :=
    ((continuous_apply t).comp (continuous_apply n)).prodMk
      ((continuous_apply (f.trans t)).comp (continuous_apply m))
  exact (isClosed_discrete {x | P x}).preimage hc

/-- **The coherent renaming of coherent choices.**  Native construction. -/
def CoherentRenaming.ofChoices (s : Choices R R')
    (hdom : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), (R.eval t).isSome ↔ (R'.eval t).isSome)
    (hs : ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (f : Fin m ↪ Fin n), IsCoherentAt s t f) :
    CoherentRenaming R R' where
  isSome_eval_iff := hdom
  renamingAt n t _ _ hp hq := (s n t).get hp hq
  faceCellMap_comm _ _ t f _ _ _ _ hp hq hp₀ hq₀ hfp hfq i := hs t f hp hq hp₀ hq₀ hfp hfq i

/-! ### Choices induced by one typed tuple -/

/-- Tuplewise renamings give a renaming at every tuple typed in both.  Native construction. -/
theorem IsCellRenamingOf.nonempty_renaming (h : R.IsCellRenamingOf R') {t : Fin n ↪ M}
    {p q : StageType.{u} α n} (hp : R.eval t = some p) (hq : R'.eval t = some q) :
    Nonempty (q.Renaming p) := by
  have ht := h t
  rw [hp, hq, Option.rel_some_some] at ht
  exact isCellRenaming_iff_nonempty_renaming.mp ht.symm

/-- The same tuples are typed in tuplewise renamed realizations.  Native construction. -/
theorem IsCellRenamingOf.isSome_eval_iff (h : R.IsCellRenamingOf R') (t : Fin n ↪ M) :
    (R.eval t).isSome ↔ (R'.eval t).isSome := by
  have ht := h t
  revert ht
  cases R.eval t <;> cases R'.eval t <;> simp

/-- A tuple whose points are points of `w` is a face of `w`.  Native construction. -/
theorem exists_trans_eq_of_forall_mem_range {w : Fin N ↪ M} {t : Fin n ↪ M}
    (ht : ∀ j, t j ∈ Set.range w) : ∃ h : Fin n ↪ Fin N, h.trans w = t := by
  choose h hh using ht
  exact ⟨⟨h, fun i j hij ↦ t.injective (by rw [← hh i, ← hh j, hij])⟩,
    Function.Embedding.ext hh⟩

open Classical in
/-- **The choices induced by a renaming at one typed tuple `w`** (native construction): at a face
`h.trans w` of `w`, the face of the renaming along `h` (`StageType.Renaming.face`); at any other
tuple typed in both, some renaming (`IsCellRenamingOf.nonempty_renaming`). -/
def inducedChoices (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hrel : R.IsCellRenamingOf R') (w : Fin N ↪ M) {P Q : StageType.{u} α N}
    (hP : R.eval w = some P) (hQ : R'.eval w = some Q) (r : Q.Renaming P) : Choices R R' :=
  fun n t ↦ RenamingOpt.mk fun _ _ hp hq ↦
    if hh : ∃ h : Fin n ↪ Fin N, h.trans w = t then
      r.face ((hR w P hh.choose hP).symm.trans
          ((congrArg (fun x ↦ R.eval x) hh.choose_spec).trans hp))
        ((hR' w Q hh.choose hQ).symm.trans
          ((congrArg (fun x ↦ R'.eval x) hh.choose_spec).trans hq))
    else Classical.choice (hrel.nonempty_renaming hp hq)

/-- The property of a face of a renaming does not depend on the name of the face. -/
private theorem faceCellMap_congr_face {P Q : StageType.{u} α N} {p q : StageType.{u} α n}
    (r : Q.Renaming P) {h h' : Fin n ↪ Fin N} (e : h' = h) (hP' : restrictFace h' P = some p)
    (hQ' : restrictFace h' Q = some q) (hP : restrictFace h P = some p)
    (hQ : restrictFace h Q = some q) (x : Fin p.card ≃ Fin q.card)
    (H : ∀ i, faceCellMap hQ' (x i) = r.toEquiv (faceCellMap hP' i)) (i : Fin p.card) :
    faceCellMap hQ (x i) = r.toEquiv (faceCellMap hP i) := by
  subst e
  exact H i

/-- **The induced choices at a face of `w`** commute with the face cell maps into `w`.
Native construction. -/
theorem faceCellMap_inducedChoices (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hrel : R.IsCellRenamingOf R') {w : Fin N ↪ M} {P Q : StageType.{u} α N}
    (hP : R.eval w = some P) (hQ : R'.eval w = some Q) (r : Q.Renaming P) {t : Fin n ↪ M}
    (h : Fin n ↪ Fin N) (hh : h.trans w = t) {p q : StageType.{u} α n}
    (hp : R.eval t = some p) (hq : R'.eval t = some q) (hPh : restrictFace h P = some p)
    (hQh : restrictFace h Q = some q) (i : Fin p.card) :
    faceCellMap hQh
        (((inducedChoices hR hR' hrel w hP hQ r n t).get hp hq).toEquiv i) =
      r.toEquiv (faceCellMap hPh i) := by
  have hex : ∃ h : Fin n ↪ Fin N, h.trans w = t := ⟨h, hh⟩
  have e : hex.choose = h :=
    Function.Embedding.ext fun j ↦ w.injective (congrFun (congrArg (⇑) (hex.choose_spec.trans
      hh.symm)) j)
  simp only [inducedChoices, RenamingOpt.get_mk, hex, dite_true]
  exact faceCellMap_congr_face r e _ _ hPh hQh _ (r.faceCellMap_face _ _) i

/-- **The induced choices are coherent at every face of `w`.**  Native construction. -/
theorem isCoherentAt_inducedChoices (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hrel : R.IsCellRenamingOf R') {w : Fin N ↪ M} {P Q : StageType.{u} α N}
    (hP : R.eval w = some P) (hQ : R'.eval w = some Q) (r : Q.Renaming P) {t : Fin n ↪ M}
    (ht : ∃ h : Fin n ↪ Fin N, h.trans w = t) (f : Fin m ↪ Fin n) :
    IsCoherentAt (inducedChoices hR hR' hrel w hP hQ r) t f := by
  intro p q p₀ q₀ hp hq hp₀ hq₀ hfp hfq i
  obtain ⟨h, rfl⟩ := ht
  have hPh : restrictFace h P = some p := (hR w P h hP).symm.trans hp
  have hQh : restrictFace h Q = some q := (hR' w Q h hQ).symm.trans hq
  apply faceCellMap_injective hQh
  rw [← faceCellMap_trans hQh hfq,
    faceCellMap_inducedChoices hR hR' hrel hP hQ r (t := f.trans (h.trans w)) (f.trans h) rfl
      hp₀ hq₀
      ((restrictFace_trans P h f hPh).symm.trans hfp),
    faceCellMap_inducedChoices hR hR' hrel hP hQ r h rfl hp hq hPh hQh, faceCellMap_trans]

/-! ### Alignment -/

/-- **Equal class readings give a coherent renaming** (native construction): for exactly
consistent realizations `R`, `R'` at the same stage on the same carrier, with `R` covering, equal
class readings give a coherent renaming of `R` into `R'`.  No receiving, no legality and no
countability of the carrier is used.

Proof: the choices of a renaming at every tuple typed in both form a compact space (Tychonoff, each
factor finite and discrete), in which coherence at each tuple and face is a closed condition.
Finitely many such conditions involve finitely many points; covering gives one typed tuple `w`
containing them, and the faces along `w` of a renaming at `w` satisfy them all
(`isCoherentAt_inducedChoices`).  By compactness some choices satisfy every condition. -/
theorem exists_coherentRenaming (hR : R.IsConsistent) (hR' : R'.IsConsistent)
    (hcov : R.IsCovering) (h : R.classReading = R'.classReading) :
    Nonempty (CoherentRenaming R R') := by
  classical
  have hrel : R.IsCellRenamingOf R' := R.classReading_eq_classReading_iff.mp h
  let ι := Σ (m n : ℕ), (Fin n ↪ M) × (Fin m ↪ Fin n)
  let T : ι → Set (Choices R R') := fun i ↦ {s | IsCoherentAt s i.2.2.1 i.2.2.2}
  have hfin : ∀ u : Finset ι, (Set.univ ∩ ⋂ i ∈ u, T i).Nonempty := by
    intro u
    -- one typed tuple containing every point of the finitely many tuples
    let S : Finset M := u.biUnion fun i ↦ Finset.univ.image i.2.2.1
    let e : Fin S.card ↪ M := S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
    obtain ⟨N, w, g, hgw, hw⟩ := hcov e
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hw
    obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp ((hrel.isSome_eval_iff w).mp hw)
    obtain ⟨r⟩ := hrel.nonempty_renaming hP hQ
    refine ⟨inducedChoices hR hR' hrel w hP hQ r, Set.mem_univ _, ?_⟩
    refine Set.mem_iInter₂.mpr fun i hi ↦ ?_
    refine isCoherentAt_inducedChoices hR hR' hrel hP hQ r
      (exists_trans_eq_of_forall_mem_range fun j ↦ ?_) i.2.2.2
    have hj : i.2.2.1 j ∈ S :=
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
    refine ⟨g (S.equivFin ⟨_, hj⟩), ?_⟩
    have := congrArg (fun x : Fin S.card ↪ M ↦ x (S.equivFin ⟨_, hj⟩)) hgw
    simpa [e] using this
  obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty T
    (fun i ↦ isClosed_setOf_isCoherentAt i.2.2.1 i.2.2.2) hfin
  exact ⟨CoherentRenaming.ofChoices s (fun _ t ↦ hrel.isSome_eval_iff t) fun m n t f ↦
    Set.mem_iInter.mp hs ⟨m, n, t, f⟩⟩

end Realization

/-! ### The alignment targets -/

/-- **Target B.T8, alignment, holds** (native construction): `AlignmentTarget β M` for every `β`
and `M`.  Only exact consistency of both realizations, covering of the first, and equality of the
class readings are used (`Realization.exists_coherentRenaming`); `β < ω₁`, countability, strongly
coded legality and receiving are not. -/
theorem alignmentTarget (β : Ordinal.{u}) (M : Type v) : AlignmentTarget β M :=
  fun _ _ _ _ hR hcov _ _ hR' _ _ _ h ↦ Realization.exists_coherentRenaming hR hR' hcov h

/-- **The reduction alignment target holds** (native construction):
`ReductionAlignmentTarget β ξ M` for every `β`, `ξ` and `M`.  The reductions to `λ_ξ` of exactly
consistent covering realizations are exactly consistent and covering, and
`Realization.exists_coherentRenaming` applies to them; the conclusion is about the reductions
only. -/
theorem reductionAlignmentTarget (β ξ : Ordinal.{u}) (M : Type v) :
    ReductionAlignmentTarget β ξ M :=
  fun _ _ _ _ _ hR hcov _ _ hR' _ _ _ h ↦
    Realization.exists_coherentRenaming (hR.reduce _) (hR'.reduce _) (hcov.reduce _) h

end

end VaughtConjecture

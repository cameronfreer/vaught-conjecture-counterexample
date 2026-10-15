/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Decoder
import VaughtConjecture.Correspondence.Sentence.Realize

/-!
# Level zero: rank-zero symbols, donors and witnesses

Numbering as in the current draft of [AFK26].  Level zero is the label stage
`blockStage 0 = ω`; a legal class `c` has rank zero when `τ₀(c) = c`.  This file states the
passages between the rank-zero quantification of clause (d) of [AFK26, Definition 4.22] and the
quantification over donors of every rank of `D[α]` [AFK26, Definition 4.20] in `K₀[L]`, each as its
own lemma, together with the facts about structures fixed by `τ₀` that B.T12 uses.

* **Faces of rank-zero classes** (`TemplateClass.restrictFace_project`,
  `TemplateClass.project_eq_of_restrictFace_eq`): projection commutes with face maps, so every face
  of a class of rank zero has rank zero.
* **Donor reduction** (`LegalClass.holds_project_of_holds`): a donor `u` of any rank whose first
  places carry a class `t` of rank zero gives the donor `τ₀(u)` of rank zero, whose first places
  still carry `t`.
* **Witness passage** (`TemplateClass.truncEquiv_project_iff`): for a cutoff `α ≤ γ ≤ ω₁`, raw
  truncation at `α` up to renaming cannot tell `d` from its projection `τ_γ(d)`; at level zero,
  for the finite cutoffs `k ∈ ω` of clause (d), `trunc_k(s) ≅_ren trunc_k(τ₀(u))` exactly when
  `trunc_k(s) ≅_ren trunc_k(u)`.  The witnesses of clause (d) and of `D[k]` are classes up to
  renaming in both places; on representatives this is `StageType.IsTruncRenaming`
  (`TemplateClass.truncEquiv_toClass_iff`).
* **Rank-zero symbols in a structure fixed by `τ₀`** (`fixed_of_relMap_invariant`): an invariant
  `Q_c` that holds somewhere has rank zero.
* **Rank-zero density** (`SatisfiesRankZeroDensityAt`): `D[α]` with the donors restricted to rank
  zero.  For a structure fixed by `τ₀` and a finite cutoff, the two are equivalent
  (`satisfiesDensityAt_iff_rankZero`): one direction is the specialization, the other the donor
  reduction followed by the witness passage.
* **Every tuple sits in a typed tuple** (`exists_relMap_invariant_comp`), in a compatible
  structure, and **`R_c` and `Q_c` agree for `c` of rank zero** (`relMap_base_iff_invariant`), in a
  compatible structure fixed by `τ₀`.

Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Classes -/

namespace TemplateClass

variable {n m : ℕ} {γ : Ordinal.{u}}

/-- **Projection of classes commutes with face maps**, including definedness.
Native construction. -/
theorem restrictFace_project (hγ : Order.IsSuccPrelimit γ) (c : TemplateClass.{u} ω₁ n)
    (f : Fin m ↪ Fin n) : (c.project hγ).restrictFace f = (c.restrictFace f).map (project hγ) :=
  Quotient.inductionOn c fun t ↦ by
    rw [project_toClass, restrictFace_toClass, restrictFace_toClass,
      StageType.restrictFace_project, Option.map_map, Option.map_map]
    rfl

/-- **The faces of a class fixed by a projection are fixed by it.**  Native construction. -/
theorem project_eq_of_restrictFace_eq (hγ : Order.IsSuccPrelimit γ) {c : TemplateClass.{u} ω₁ n}
    (hc : c.project hγ = c) {f : Fin m ↪ Fin n} {s : TemplateClass.{u} ω₁ m}
    (hs : c.restrictFace f = some s) : s.project hγ = s := by
  have h := restrictFace_project hγ c f
  rw [hc, hs, Option.map_some] at h
  exact (Option.some.inj h).symm

/-- **Witness passage**: for `α ≤ γ ≤ ω₁`, raw truncation at `α` up to renaming does not see the
projection to `γ`: `trunc_α(c) ≅_ren trunc_α(τ_γ(d))` exactly when `trunc_α(c) ≅_ren trunc_α(d)`.
Correspondence with the printed definitions. -/
theorem truncEquiv_project_iff {α : Ordinal.{u}} (hγ : Order.IsSuccPrelimit γ) (hγω : γ ≤ ω₁)
    (hα : α ≤ γ) (c d : TemplateClass.{u} ω₁ n) :
    c.TruncEquiv α (d.project hγ) ↔ c.TruncEquiv α d := by
  induction c using Quotient.inductionOn with | h s => ?_
  induction d using Quotient.inductionOn with | h t => ?_
  change s.toClass.TruncEquiv α (t.project hγ).toClass ↔ s.toClass.TruncEquiv α t.toClass
  rw [truncEquiv_toClass_iff, truncEquiv_toClass_iff]
  refine exists_congr fun s' ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    forall_congr' fun i ↦ forall_congr' fun j ↦ imp_congr_right fun _ ↦ ?_
  rw [t.label_project hγ hγω j]
  have key : Label.reduce α (Label.reduce γ (t.label j)) = Label.reduce α (t.label j) :=
    Label.reduce_reduce_of_le hα _
  exact Iff.of_eq (congrArg (fun z ↦ Label.reduce α (s'.label i) = z) key)

end TemplateClass

/-! ### Donors -/

namespace LegalClass

variable {n m : ℕ}

/-- A legal class of rank zero: `τ₀(c) = c`.  Correspondence with the printed definitions. -/
def IsRankZero {n : ℕ} (c : LegalClass.{u} n) : Prop :=
  c.1.project (isSuccPrelimit_blockStage 0) = c.1

/-- The projection `τ₀(c)` has rank zero.  Correspondence with the printed definitions. -/
theorem isRankZero_project (c : LegalClass.{u} n) : (c.project 0).IsRankZero :=
  congrArg Subtype.val (c.project_project (β := 0))

/-- A class of rank zero is its own projection.  Native construction. -/
theorem project_eq_self {c : LegalClass.{u} n} (hc : c.IsRankZero) : c.project 0 = c :=
  Subtype.ext hc

/-- **Donor reduction**: if the first `n` places of a donor `u` (of any rank) carry a class `t`
of rank zero, so do the first `n` places of the rank-zero donor `τ₀(u)`.
Correspondence with the printed definitions. -/
theorem holds_project_of_holds {t : LegalClass.{u} n} (ht : t.IsRankZero) (hn : 0 < n)
    {u : LegalClass.{u} (n + m)}
    (hu : u.1.Holds (TemplateSymbol.invariant t hn) (Fin.castAdd m)) :
    (u.project 0).1.Holds (TemplateSymbol.invariant t hn) (Fin.castAdd m) := by
  obtain ⟨h, s, hs, hst⟩ := hu
  refine ⟨h, s.project (isSuccPrelimit_blockStage 0), ?_, ?_⟩
  · rw [coe_project, TemplateClass.restrictFace_project, hs, Option.map_some]
  · change s.project _ = t.1
    rw [show s = t.1 from hst]
    exact ht

end LegalClass

/-! ### Structures fixed by `τ₀` -/

variable {M : Type v} {G : templateLanguage.{u}.Structure M}

/-- **Rank-zero invariants**: in a structure fixed by `τ₀`, an invariant `Q_c` that holds of some
tuple has rank zero.  Correspondence with the printed definitions. -/
theorem fixed_of_relMap_invariant (hG : projectStructure 0 G = G) {n : ℕ} {c : LegalClass.{u} n}
    {hn : 0 < n} {x : Fin n → M}
    (h : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) x) :
    c.IsRankZero := by
  have h' : RelMap (L := templateLanguage.{u}) (self := projectStructure 0 G)
      (TemplateSymbol.invariant c hn) x := by
    rw [hG]
    exact h
  obtain ⟨c', rfl, -⟩ := h'
  exact c'.isRankZero_project

/-- **`D[α]` with rank-zero donors**: as `SatisfiesDensityAt α G`, with the donor `u` restricted to
classes of rank zero.  Correspondence with the printed definitions. -/
def SatisfiesRankZeroDensityAt (α : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)), u.IsRankZero →
    u.1.Holds (TemplateSymbol.invariant t hn) (Fin.castAdd m) →
    ∀ x : Fin n → M,
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant t hn) x →
      ∃ (y : Fin m → M) (s : LegalClass.{u} (n + m)), s.1.TruncEquiv α u.1 ∧
        RelMap (L := templateLanguage.{u}) (self := G)
          (TemplateSymbol.invariant s (Nat.lt_add_right m hn)) (Fin.append x y)

/-- **Density with donors of every rank gives density with rank-zero donors** (specialization).
Correspondence with the printed definitions. -/
theorem SatisfiesDensityAt.rankZero {α : Ordinal.{u}} (h : SatisfiesDensityAt α G) :
    SatisfiesRankZeroDensityAt α G := by
  intro n m hn t u _ hu x hx
  rw [satisfiesDensityAt_iff] at h
  exact h hn t u hu x hx

/-- **Density with rank-zero donors gives density with donors of every rank**, at a cutoff
`α ≤ ω`, in a structure fixed by `τ₀`: a donor `u` is replaced by `τ₀(u)` (donor reduction,
`LegalClass.holds_project_of_holds`), and the witness for `τ₀(u)` is a witness for `u` (witness
passage, `TemplateClass.truncEquiv_project_iff`).  Correspondence with the printed definitions. -/
theorem satisfiesDensityAt_of_rankZero (hG : projectStructure 0 G = G) {α : Ordinal.{u}}
    (hα : α ≤ ω) (h : SatisfiesRankZeroDensityAt α G) : SatisfiesDensityAt α G := by
  rw [satisfiesDensityAt_iff]
  intro n m hn t u hu x hx
  obtain ⟨y, s, hs, hxy⟩ := h hn t (u.project 0) u.isRankZero_project
    (LegalClass.holds_project_of_holds (fixed_of_relMap_invariant hG hx) hn hu) x hx
  refine ⟨y, s, ?_, hxy⟩
  rw [LegalClass.coe_project] at hs
  exact (TemplateClass.truncEquiv_project_iff _
    (by rw [blockStage_zero]; exact omega0_lt_omega_one.le) (by rwa [blockStage_zero]) _ _).mp hs

/-! ### Compatible structures -/

/-- An invariant symbol is some `Q_c`.  Native construction. -/
theorem TemplateSymbol.exists_eq_invariant {k : ℕ} {r : TemplateSymbol.{u} k}
    (h : r.IsInvariant) : ∃ (c : LegalClass.{u} k) (hk : 0 < k), r = .invariant c hk := by
  cases r with
  | invariant c hk => exact ⟨c, hk, rfl⟩
  | closed => exact h.elim
  | base => exact h.elim

/-- **Every tuple sits in a typed tuple**, in a compatible structure: for `k ≥ 1`, every
`x : Fin k → M` is `y ∘ i` for some tuple `y` with an invariant `Q_c` (the distinct points of `x`
extend to a closed tuple, [AFK26, Definition 2.1], second clause).
Correspondence with the printed definitions. -/
theorem exists_relMap_invariant_comp (hG : IsTemplateCompatible G) {k : ℕ} (hk : 0 < k)
    (x : Fin k → M) :
    ∃ (N : ℕ) (hN : 0 < N) (c : LegalClass.{u} N) (y : Fin N → M) (i : Fin k → Fin N),
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hN) y ∧
        y ∘ i = x := by
  classical
  set S : Finset M := Finset.univ.image x
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨x ⟨0, hk⟩, Finset.mem_image_of_mem _ (by simp)⟩
  let e : Fin S.card → M := fun j ↦ (S.equivFin.symm j).1
  have he : Function.Injective e := fun a b h ↦ S.equivFin.symm.injective (Subtype.ext h)
  obtain ⟨K, y, hy, hP⟩ := hG.isStructuredGeometry.isGeometry.exists_closed hS e he
  obtain ⟨Q, hQ, hQy⟩ := (hG.isStructuredGeometry.closed_iff _ y).mp hP
  obtain ⟨c, hN, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
  refine ⟨_, hN, c, y, fun j ↦ Fin.castAdd K (S.equivFin ⟨x j, by simp [S]⟩), hQy,
    funext fun j ↦ ?_⟩
  have := congrFun hy (S.equivFin ⟨x j, by simp [S]⟩)
  simpa [e] using this

/-- **`R_c` and `Q_c` agree for `c` of rank zero**, in a compatible structure fixed by `τ₀`.
Correspondence with the printed definitions. -/
theorem relMap_base_iff_invariant (hG : IsTemplateCompatible G) (hfix : projectStructure 0 G = G)
    {n : ℕ} (c : LegalClass.{u} n) (h0 : c.IsRankZero) (hn : 0 < n) (x : Fin n → M) :
    RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.base c h0 hn) x ↔
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) x := by
  constructor
  · intro hR
    obtain ⟨N, hN, d, y, i, hy, rfl⟩ := exists_relMap_invariant_comp hG hn x
    obtain ⟨hi, s, hs, -⟩ := (hG.relMap_comp_iff hy _ i).mp hR
    have hP : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hn) (y ∘ i) :=
      (hG.relMap_comp_iff hy _ i).mpr ⟨hi, s, hs, trivial⟩
    obtain ⟨Q, hQ, hQx⟩ := (hG.isStructuredGeometry.closed_iff hn _).mp hP
    obtain ⟨e, hn', rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
    have he := fixed_of_relMap_invariant hfix hQx
    obtain ⟨_, s', hs', hread⟩ :=
      (hG.relMap_comp_iff hQx (TemplateSymbol.base c h0 hn) id).mp hR
    have hs'e : s' = e.1 := by
      have := e.1.restrictFace_refl
      exact Option.some.inj ((Eq.symm hs').trans this)
    have hec : e = c := by
      refine Subtype.ext ?_
      change s'.project _ = c.1 at hread
      rw [hs'e, show e.1.project _ = e.1 from he] at hread
      exact hread
    subst hec
    exact hQx
  · intro hQ
    exact (hG.relMap_comp_iff hQ _ id).mpr
      ⟨Function.injective_id, c.1, c.1.restrictFace_refl, h0⟩

/-- **Clause (d) of [AFK26, Definition 4.22] is rank-zero density**: for a compatible structure
`G` fixed by `τ₀`, its base reduct satisfies clause (d) exactly when `G` satisfies `D[k]` with
rank-zero donors for every `k ∈ ω`.  The symbols `R_t` of clause (d) are read as the invariants
`Q_t` (`relMap_base_iff_invariant`), and its witnesses, symbols of `L_c[L]`, are the witnesses of
`D[k]`, which have rank zero (`fixed_of_relMap_invariant`).
Correspondence with the printed definitions. -/
theorem density_baseReduct_iff (hG : IsTemplateCompatible G) (hfix : projectStructure 0 G = G) :
    (∀ (k n m : ℕ) (tt : DensityIndex.{u} n m) (x : Fin (n + 1) → M),
        @ClassRel _ (baseReduct G) _ tt.1.1 x →
        ∃ (y : Fin m → M) (s : ClassSymbol.{u} (n + 1 + m)), s.1.1.TruncEquiv k tt.1.2.1.1 ∧
          RelMap (L := baseTemplateLanguage.{u}) (self := baseReduct G)
            (s.toBaseSymbol (Nat.lt_add_right m n.succ_pos)) (Fin.append x y)) ↔
      ∀ k : ℕ, SatisfiesRankZeroDensityAt (k : Ordinal.{u}) G := by
  constructor
  · intro h k n m hn t u hu hpair x hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    have ht := fixed_of_relMap_invariant hfix hx
    obtain ⟨y, s, hs, hy⟩ := h k n m ⟨(⟨t, ht⟩, ⟨u, hu⟩), hpair⟩ x
      ((relMap_base_iff_invariant hG hfix t ht _ x).mpr hx)
    exact ⟨y, s.1, hs, (relMap_base_iff_invariant hG hfix s.1 s.2 _ _).mp hy⟩
  · intro h k n m tt x hx
    obtain ⟨y, s, hs, hy⟩ := h k n.succ_pos tt.1.1.1 tt.1.2.1 tt.1.2.2 tt.2 x
      ((relMap_base_iff_invariant hG hfix _ tt.1.1.2 _ x).mp hx)
    have hs0 := fixed_of_relMap_invariant hfix hy
    exact ⟨y, ⟨s, hs0⟩, hs, (relMap_base_iff_invariant hG hfix s hs0 _ _).mpr hy⟩

end

end VaughtConjecture

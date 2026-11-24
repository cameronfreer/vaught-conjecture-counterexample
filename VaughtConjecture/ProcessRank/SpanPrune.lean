/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanTargets

/-!
# Pruning a span of mutual forcing

Process rank `ω₁`, the finite span of mutual rigidity: the pruning step.

**Faces of types agreeing on the visible cells** (`StageType.restrictFace_eq_of_toScheme_eq`).  Two
stage types on one scheme whose labels agree at the cells visible through `f` have the same face
along `f`.

**Admissible top supports of a witness** (`StageType.IsAdmissibleTopSupport.of_witness`).  Let
`E` be a witness that `H` is an admissible top support of `D`, on the scheme of `D`.  Every
admissible top support of `E` is one of `D`: a cell not labelled `⊤` in `D` keeps its label in
`E`, a top cell of `D` outside `H` is proper in `E`, and a witness for `E` keeps the proper labels
of `E` and makes the top cells of `E` outside the support proper.

**Pruning** (`StageType.pruneTarget`, proving `StageType.PruneTarget`).  In a legal `D` in which
the cores along `i` and `j` force the top cells of each other, choose an admissible top support
`H` of `D` containing the top cells visible through `i`, of least cardinality (the top cells of a
legal type form one, `StageType.isAdmissibleTopSupport_top`), and a witness `E`.  It contains the
top cells visible through `j` (forcing), so `E` has the faces of `D` along `i` and `j`.  An
admissible top support `H'` of `E` containing the top cells of `E` visible through `i` is one of
`D` containing the top cells visible through `i`, and lies in the top cells `H` of `E`; by
minimality it is `H`, so the core along `i` is rigid in `E`.  If `H'` contains the top cells of
`E` visible through `j`, it contains the top cells of `D` visible through `j`, hence (forcing)
those visible through `i`, and the same argument applies.  Only the definition of an admissible
top support enters; the stage is arbitrary.  With pruning proved, the construction of mutual
forcing alone gives spans of mutual rigidity
(`StageType.mutualRigidSpanTarget_of_mutualForcingSpanTarget`).
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n m : ℕ}

/-- **Faces of types agreeing on the visible cells**: two stage types on one scheme whose labels
agree, at equal positions, at the cells visible through `f` have the same face along `f`. -/
theorem restrictFace_eq_of_toScheme_eq {t t' : StageType.{u} α m} (hs : t.toScheme = t'.toScheme)
    (f : Fin n ↪ Fin m)
    (hl : ∀ (a : Fin t.card) (b : Fin t'.card), (a : ℕ) = b → a ∈ t.visibleCells f →
      t.label a = t'.label b) :
    restrictFace f t = restrictFace f t' := by
  obtain ⟨S, ℓ, h₁, h₂, h₃, h₄⟩ := t
  obtain ⟨S', ℓ', h₁', h₂', h₃', h₄'⟩ := t'
  change S = S' at hs
  subst hs
  by_cases hf : univ.map f ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ f hf, restrictFace_of_mem _ f hf]
    refine congrArg some (ext rfl fun a b hab ↦ ?_)
    obtain rfl : a = b := Fin.ext hab
    refine hl _ _ rfl ?_
    have h := Set.mem_range_self (f := S.cellMap f) a
    rw [Scheme.range_cellMap] at h
    exact_mod_cast h
  · rw [restrictFace_of_notMem _ f hf, restrictFace_of_notMem _ f hf]

/-- **Admissible top supports of a witness**: if `E`, on the scheme of `D`, witnesses that `H` is
an admissible top support of `D`, every admissible top support of `E` is one of `D`. -/
theorem IsAdmissibleTopSupport.of_witness {D : StageType.{u} α m} {H : Set (Fin D.card)}
    {E : StageType.{u} α m} (hs : E.toScheme = D.toScheme)
    (hE : ∀ (a : Fin E.card) (b : Fin D.card), (a : ℕ) = b →
      (D.label b ≠ ⊤ → E.label a = D.label b) ∧ (E.label a = ⊤ ↔ b ∈ H) ∧
        (D.label b = ⊤ → b ∉ H → (E.label a).IsProper))
    {H' : Set (Fin D.card)}
    (h' : E.IsAdmissibleTopSupport {a | ∃ b ∈ H', (a : ℕ) = b}) :
    D.IsAdmissibleTopSupport H' := by
  obtain ⟨F, hF, hFs, hFw⟩ := h'
  have hc : E.card = D.card := congrArg Scheme.card hs
  refine ⟨F, hF, hFs.trans hs, fun a b hab ↦ ?_⟩
  set e : Fin E.card := Fin.cast hc.symm b with he
  have heb : (e : ℕ) = b := rfl
  obtain ⟨hFn, hFt, hFp⟩ := hFw a e (hab.trans heb.symm)
  obtain ⟨hEn, hEt, hEp⟩ := hE e b heb
  have hmem : e ∈ {a : Fin E.card | ∃ b ∈ H', (a : ℕ) = b} ↔ b ∈ H' :=
    ⟨fun ⟨b', hb', h⟩ ↦ by rwa [show b = b' from Fin.ext (heb.symm.trans h)],
      fun hb ↦ ⟨b, hb, heb⟩⟩
  refine ⟨fun hb ↦ ?_, hFt.trans hmem, fun hb hbH' ↦ ?_⟩
  · rw [← hEn hb]
    exact hFn (by rw [hEn hb]; exact hb)
  · by_cases hbH : b ∈ H
    · exact hFp (hEt.mpr hbH) (hmem.not.mpr hbH')
    · have hp := hEp hb hbH
      rw [hFn ((isProper_iff_ne.mp hp).2)]
      exact hp

/-- **Pruning**: in a legal stage type in which two cores force the top cells of each other, a
witness of an admissible top support of least cardinality containing the top cells of the first
core is a legal type on the same scheme, with the same two faces, in which both cores are
rigid. -/
theorem pruneTarget : PruneTarget.{u} := by
  intro α n m D i j hD hij hji
  classical
  set Ti : Finset (Fin D.card) := univ.filter fun d ↦ d ∈ D.visibleCells i ∧ D.label d = ⊤
    with hTi
  set 𝓗 : Finset (Finset (Fin D.card)) :=
    univ.filter fun H ↦ D.IsAdmissibleTopSupport (H : Set (Fin D.card)) ∧ Ti ⊆ H with h𝓗
  have hmem𝓗 {H : Finset (Fin D.card)} :
      H ∈ 𝓗 ↔ D.IsAdmissibleTopSupport (H : Set (Fin D.card)) ∧ Ti ⊆ H := by
    simp [h𝓗]
  have hne : 𝓗.Nonempty := by
    refine ⟨univ.filter (D.label · = ⊤), hmem𝓗.mpr ⟨?_, fun d hd ↦ ?_⟩⟩
    · convert isAdmissibleTopSupport_top hD using 1
      ext d
      simp
    · simp only [hTi, mem_filter, mem_univ, true_and] at hd ⊢
      exact hd.2
  obtain ⟨H, hH, hmin⟩ := 𝓗.exists_min_image Finset.card hne
  obtain ⟨hHadm, hTiH⟩ := hmem𝓗.mp hH
  -- the forced top cells along `j` lie in `H`
  have hTjH : ∀ d ∈ D.visibleCells j, D.label d = ⊤ → d ∈ H := fun d hd htop ↦
    hij _ hHadm (fun d' hd' ht' ↦ hTiH (mem_filter.mpr ⟨mem_univ _, hd', ht'⟩)) d hd htop
  obtain ⟨E, hEl, hs, hw⟩ := hHadm
  obtain ⟨S', ℓ', h₁, h₂, h₃, h₄⟩ := E
  change S' = D.toScheme at hs
  subst hs
  set E : StageType.{u} α m := ⟨D.toScheme, ℓ', h₁, h₂, h₃, h₄⟩ with hEdef
  have hEtop (d : Fin D.card) : E.label d = ⊤ ↔ d ∈ H := by
    simpa using (hw d d rfl).2.1
  have hEn (d : Fin D.card) (hd : D.label d ≠ ⊤) : E.label d = D.label d := (hw d d rfl).1 hd
  -- admissible top supports of `E` are admissible top supports of `D`
  have hadm (H' : Set (Fin D.card)) (h' : E.IsAdmissibleTopSupport H') :
      D.IsAdmissibleTopSupport H' := by
    refine IsAdmissibleTopSupport.of_witness (D := D) (H := (H : Set (Fin D.card))) (E := E) rfl
      (fun a b hab ↦ ?_) ?_
    · obtain rfl : a = b := Fin.ext hab
      exact hw a a rfl
    · convert h' using 1
      ext a
      exact ⟨fun ⟨b, hb, h⟩ ↦ (show a = b from Fin.ext h) ▸ hb, fun h ↦ ⟨a, h, rfl⟩⟩
  -- an admissible support of `E` containing `Ti` contains every top cell of `E`
  have hkey (H' : Set (Fin D.card)) (h' : E.IsAdmissibleTopSupport H') (hTi' : ∀ d ∈ Ti, d ∈ H')
      (d : Fin D.card) (hd : E.label d = ⊤) : d ∈ H' := by
    have hsub : H' ⊆ H := fun e he ↦ (hEtop e).mp (h'.subset he)
    set H'f := H'.toFinset with hH'f
    have hH'f : (H'f : Set (Fin D.card)) = H' := Set.coe_toFinset H'
    have hmemf : H'f ∈ 𝓗 :=
      hmem𝓗.mpr ⟨hH'f ▸ hadm H' h', fun e he ↦ Set.mem_toFinset.mpr (hTi' e he)⟩
    have hle : H.card ≤ H'f.card := hmin H'f hmemf
    have hsubf : H'f ⊆ H := fun e he ↦ hsub (Set.mem_toFinset.mp he)
    have heq : H'f = H := eq_of_subset_of_card_le hsubf hle
    have hdH := (hEtop d).mp hd
    rw [← heq] at hdH
    exact Set.mem_toFinset.mp hdH
  refine ⟨E, hEl, rfl, ?_, ?_, ?_, ?_⟩
  · refine restrictFace_eq_of_toScheme_eq (t := E) (t' := D) rfl i fun a b hab ha ↦ ?_
    obtain rfl : a = b := Fin.ext hab
    by_cases ht : D.label a = ⊤
    · exact ((hEtop a).mpr (hTiH (mem_filter.mpr ⟨mem_univ _, ha, ht⟩))).trans ht.symm
    · exact hEn a ht
  · refine restrictFace_eq_of_toScheme_eq (t := E) (t' := D) rfl j fun a b hab ha ↦ ?_
    obtain rfl : a = b := Fin.ext hab
    by_cases ht : D.label a = ⊤
    · exact ((hEtop a).mpr (hTjH a ha ht)).trans ht.symm
    · exact hEn a ht
  · intro H' h' hcore d hd
    refine hkey H' h' (fun e he ↦ ?_) d hd
    simp only [hTi, mem_filter, mem_univ, true_and] at he
    exact hcore e he.1 ((hEtop e).mpr (hTiH (mem_filter.mpr ⟨mem_univ _, he.1, he.2⟩)))
  · intro H' h' hcore d hd
    refine hkey H' h' (fun e he ↦ ?_) d hd
    simp only [hTi, mem_filter, mem_univ, true_and] at he
    refine hji H' (hadm H' h') (fun e' he' ht' ↦ hcore e' he' ?_) e he.1 he.2
    exact (hEtop e').mpr (hTjH e' he' ht')

/-- **Spans of mutual rigidity from the construction of mutual forcing**: with pruning proved, the
construction target alone gives spans of mutual rigidity.  Proved, conditional on
`StageType.MutualForcingSpanTarget`. -/
theorem mutualRigidSpanTarget_of_mutualForcingSpanTarget (h : MutualForcingSpanTarget.{u}) :
    MutualRigidSpanTarget.{u} :=
  mutualRigidSpanTarget_of_prune pruneTarget h

end VaughtConjecture.StageType

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.StronglyCodedCompletion

/-!
# Amalgamation within the strongly coded legal stage types

Roadmap, Correspondence, item 1 (the legal templates of [AFK26]) and Layer 3, 3.1, (R6); semantic
contract, items 3–4.

**The class.**  `StageType.IsStronglyCodedLegal t`: `t` is legal and its rows are strongly coded
(`CellScheme.Rows.IsStronglyCoded`, the range clause of [AFK26, Definition "legal"]).  In the
fixed-rows reading of the templates of [AFK26] (roadmap, Correspondence, item 1), the legal
templates of [AFK26] are these stage types; that identification is not proved here.  Legality
(`Scheme.IsLegal`) is not changed.

**Closure.**  Within this class, at every stage that is zero or a limit:

* **restriction** to a defined face stays in the class (`StageType.isStronglyCoded_of_restrictFace`
  with `StageType.IsLegal.restrictFace`), the hereditary property;
* the **coatom extension property with apex** holds
  (`StageType.hasStronglyCodedApexCoatomExtensions`): the amalgam of the two coatom types, its
  completion below the full grade, and the strongly coded apex
  (`VaughtConjecture.Extension.StronglyCodedCompletion`);
* the **exact pinned extension** (`StageType.exists_stronglyCoded_pinned_extension`), the
  **amalgamation over a common face** (`StageType.exists_stronglyCoded_amalgam`,
  `StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit`), and **joint embedding**
  (`StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit`), by the arguments of
  `StageType.exists_pinned_extension_of_lt` and `StageType.exists_amalgam` with the class carried
  through.  At a face along a surjective embedding, the extension of
  `StageType.exists_pinned_extension_of_surjective` is reused: a stage type whose face along a
  surjective embedding is strongly coded is strongly coded
  (`StageType.isStronglyCoded_of_restrictFace_of_surjective`).

So the strongly coded legal stage types support the finite extension and amalgamation
constructions directly, with no conversion of the inputs; the amalgam they receive is built by the
construction of `StageType.exists_amalgam`, except that the row of the apex is the strongly coded
encoding of the labels.

**Not proved here.**  The correspondence between these stage types and the charts of [AFK26]
(their language, embeddings, and truncation), and the Fraïssé limit of the age of their charts.

## References

The hereditary, joint embedding, and amalgamation properties are those of [AFK26, Proposition
"Charts have (HP) (JEP) (AP)"], for the legal templates of [AFK26, Definition "legal"]; the coatom
extension with apex is [Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Strong coding along faces -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **A defined face of a strongly coded stage type is strongly coded.** -/
theorem isStronglyCoded_of_restrictFace {t : StageType.{u} α n} {s : StageType.{u} α m}
    {f : Fin m ↪ Fin n} (h : restrictFace f t = some s) (ht : t.rows.IsStronglyCoded) :
    s.rows.IsStronglyCoded := by
  have hc := Scheme.isStronglyCoded_comap ht f
  rwa [comap_toScheme_of_restrictFace h] at hc

/-- **A stage type with a strongly coded face along a surjective embedding is strongly coded**:
every cell is visible through the embedding. -/
theorem isStronglyCoded_of_restrictFace_of_surjective {t : StageType.{u} α n}
    {s : StageType.{u} α m} {f : Fin m ↪ Fin n} (h : restrictFace f t = some s)
    (hf : Function.Surjective f) (hs : s.rows.IsStronglyCoded) : t.rows.IsStronglyCoded := by
  have hc : (t.toScheme.comap f).rows.IsStronglyCoded := by
    rw [comap_toScheme_of_restrictFace h]
    exact hs
  intro d
  refine Scheme.isStronglyCodedAt_of_comap hc ?_
  rw [Scheme.mem_visibleCells]
  exact fun x _ ↦ hf x

/-- A stage type is **strongly coded legal** when it is legal and its rows are strongly coded: every
row entry at a cell of grade `g` is bottom or `ω · n + i` with `i ≤ g + 1`, the range clause of
[AFK26, Definition "legal"]. -/
def IsStronglyCodedLegal (t : StageType.{u} α n) : Prop := t.IsLegal ∧ t.rows.IsStronglyCoded

variable (α) in
/-- The **coatom extension property with apex within the strongly coded legal stage types**:
`StageType.HasApexCoatomExtensions` with strongly coded inputs and a strongly coded output. -/
def HasStronglyCodedApexCoatomExtensions : Prop :=
  ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m), ta.IsStronglyCodedLegal →
    tb.IsStronglyCodedLegal → restrictFace Fin.castSuccEmb ta = some p →
    restrictFace Fin.castSuccEmb tb = some p →
    ∃ t : StageType.{u} α (m + 2), t.IsStronglyCodedLegal ∧
      restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d

end StageType

/-! ### The strongly coded completion of a seed -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- The **strongly coded completion** of a seed at a stage that is zero or a limit: the truncation
with the strongly coded apex added (`StageType.addStrongApex`). -/
noncomputable def strongCompletion : StageType.{u} α (m + 2) :=
  (F.truncate hα).addStrongApex F.isLegalBelowFullGrade (Nat.succ_pos _)

include F hα in
/-- **The strongly coded coatom extension from a strongly coded completion below the full grade**:
a legal stage type on `m + 2` points with strongly coded rows whose faces along the two coatoms
are the coatom types of `I`, with a cell of full scope and full grade carrying the largest
label. -/
theorem exists_stronglyCodedCoatomExtension (hF : F.scheme.rows.IsStronglyCoded) :
    ∃ t : StageType.{u} α (m + 2), t.IsStronglyCodedLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some I.left ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some I.right ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d :=
  ⟨F.strongCompletion hα,
    ⟨StageType.isLegal_addStrongApex _ _, StageType.isStronglyCoded_addStrongApex _ _ hF⟩,
    (StageType.restrictFace_addStrongApex _ _ _ Coatom.univ_map_left_ne).trans
      (F.restrictFace_left_truncate hα),
    (StageType.restrictFace_addStrongApex _ _ _ Coatom.univ_map_right_ne).trans
      ((F.restrictFace_withLabel _ _ (F.truncate_label_embed hα) _ Coatom.univ_map_right_ne).trans
        I.restrictFace_right),
    StageType.exists_apex_addStrongApex _ _⟩

end CompletionBelowFullGrade

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **The coatom extension property with apex holds within the strongly coded legal stage types**
at every stage that is zero or a limit: the amalgam of two strongly coded coatom types is strongly
coded (`Seed.isStronglyCoded_amalgam`), its completion below the full grade is strongly coded
(`Seed.exists_completionBelowFullGrade_isStronglyCoded`), and the strongly coded apex keeps strong
coding (`StageType.isStronglyCoded_addStrongApex`). -/
theorem hasStronglyCodedApexCoatomExtensions (hα : Order.IsSuccPrelimit α) :
    HasStronglyCodedApexCoatomExtensions.{u} α := fun _ _ _ _ hla hlb hpa hpb ↦
  let I := Seed.ofCoatoms hla.1 hlb.1 hpa hpb
  let ⟨F, hF⟩ := I.exists_completionBelowFullGrade_isStronglyCoded
    (I.isStronglyCoded_amalgam hla.2 hlb.2)
  F.exists_stronglyCodedCoatomExtension hα hF

/-! ### Pinned extensions and amalgamation within the class -/

/-- **The exact pinned extension within the strongly coded legal stage types**, from strongly coded
coatom extensions below the arity: as `StageType.exists_pinned_extension_of_lt`. -/
theorem exists_stronglyCoded_pinned_extension_of_lt
    (hext : ∀ m' < n, ∀ (ta tb : StageType.{u} α (m' + 1)) (p : StageType.{u} α m'),
      ta.IsStronglyCodedLegal → tb.IsStronglyCodedLegal →
        restrictFace Fin.castSuccEmb ta = some p → restrictFace Fin.castSuccEmb tb = some p →
          ∃ t : StageType.{u} α (m' + 2), t.IsStronglyCodedLegal ∧
            restrictFace Fin.castSuccEmb t = some ta ∧
            restrictFace (extendByLast Fin.castSuccEmb) t = some tb)
    {P : StageType.{u} α n} (hP : P.IsStronglyCodedLegal) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p)
    (hd : d.IsStronglyCodedLegal) (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsStronglyCodedLegal ∧
      restrictFace Fin.castSuccEmb Q = some P ∧ restrictFace (extendByLast f) Q = some d := by
  induction hk : n - m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    subst hk
    by_cases hsurj : Function.Surjective f
    · obtain ⟨Q, hQ, hQP, hQd⟩ := exists_pinned_extension_of_surjective hsurj hPf hd.1 hdp
      have hsurj' : Function.Surjective (extendByLast f) := fun y ↦ by
        induction y using Fin.lastCases with
        | last => exact ⟨Fin.last m, by simp⟩
        | cast y =>
          obtain ⟨i, rfl⟩ := hsurj y
          exact ⟨i.castSucc, by simp⟩
      exact ⟨Q, ⟨hQ, isStronglyCoded_of_restrictFace_of_surjective hQd hsurj' hd.2⟩, hQP, hQd⟩
    have hfP : univ.map f ∈ P.toCellScheme.faces := ((restrictFace_eq_some_iff P f).mp hPf).1
    have hplan := P.isWellFormed.isWellFormed.isPlan
    rw [P.isWellFormed.ground_eq] at hplan
    have hne : univ.map f ≠ univ := fun he ↦ hsurj fun y ↦ by
      have hy : y ∈ univ.map f := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxP⟩ := hplan.exists_insert_mem hfP hne
    have hx' : x ∉ Set.range f := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set f' := Fin.Embedding.snoc f hx'
    have hff' : Fin.castSuccEmb.trans f' = f := Fin.Embedding.init_snoc f hx'
    have hf'P : univ.map f' ∈ P.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    set p' := P.comap f' hf'P
    have hPf' : restrictFace f' P = some p' := restrictFace_of_mem P f' hf'P
    have hp' : p'.IsStronglyCodedLegal :=
      ⟨hP.1.restrictFace f' hPf', isStronglyCoded_of_restrictFace hPf' hP.2⟩
    have hp'p : restrictFace Fin.castSuccEmb p' = some p := by
      rw [restrictFace_trans P f' _ hPf', hff', hPf]
    have hmn : m < n := by
      have hle : m ≤ n := by simpa using Fintype.card_le_of_embedding f
      refine lt_of_le_of_ne hle fun he ↦ hsurj ?_
      exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp [he]⟩).2
    obtain ⟨t, ht, htp', htd⟩ := hext m hmn p' d p hp' hd hp'p hdp
    obtain ⟨Q, hQ, hQP, hQt⟩ := ih (n - (m + 1)) (by omega) hPf' ht htp' rfl
    refine ⟨Q, hQ, hQP, ?_⟩
    rw [← hff', ← extendByLast_trans, ← restrictFace_trans Q _ _ hQt, htd]

/-- **The exact pinned extension within the strongly coded legal stage types**, from the
strongly coded coatom extension property. -/
theorem exists_stronglyCoded_pinned_extension (hext : HasStronglyCodedApexCoatomExtensions.{u} α)
    {P : StageType.{u} α n} (hP : P.IsStronglyCodedLegal) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p)
    (hd : d.IsStronglyCodedLegal) (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsStronglyCodedLegal ∧
      restrictFace Fin.castSuccEmb Q = some P ∧ restrictFace (extendByLast f) Q = some d :=
  exists_stronglyCoded_pinned_extension_of_lt
    (fun m' _ ta tb p hta htb hpa hpb ↦
      let ⟨t, ht, hta', htb', _⟩ := hext m' ta tb p hta htb hpa hpb
      ⟨t, ht, hta', htb'⟩) hP hPf hd hdp

/-- **Amalgamation over a common face within the strongly coded legal stage types**, from the
strongly coded coatom extension property: as `StageType.exists_amalgam`, with strongly coded
inputs and a strongly coded output. -/
theorem exists_stronglyCoded_amalgam (hext : HasStronglyCodedApexCoatomExtensions.{u} α)
    {P : StageType.{u} α n} {R : StageType.{u} α k} (hP : P.IsStronglyCodedLegal)
    (hR : R.IsStronglyCodedLegal) {f : Fin m ↪ Fin n} {g : Fin m ↪ Fin k}
    {p : StageType.{u} α m} (hPf : restrictFace f P = some p) (hRg : restrictFace g R = some p) :
    ∃ (N : ℕ) (Q : StageType.{u} α N) (i : Fin n ↪ Fin N) (j : Fin k ↪ Fin N),
      Q.IsStronglyCodedLegal ∧ restrictFace i Q = some P ∧ restrictFace j Q = some R ∧
      f.trans i = g.trans j := by
  induction hk : k - m using Nat.strong_induction_on generalizing n m P f with
  | _ l ih =>
    subst hk
    by_cases hsurj : Function.Surjective g
    · set G := Equiv.ofBijective g ⟨g.injective, hsurj⟩
      have hRp : p.reindex G.symm = R := by
        have h := map_reindex_restrictFace R g G.symm
        rw [hRg, Option.map_some] at h
        have hid : G.symm.toEmbedding.trans g = Function.Embedding.refl (Fin k) :=
          Function.Embedding.ext fun i ↦ G.apply_symm_apply i
        rw [hid, restrictFace_refl] at h
        exact Option.some_injective _ h
      refine ⟨n, P, Function.Embedding.refl _, G.symm.toEmbedding.trans f, hP, restrictFace_refl P,
        ?_, ?_⟩
      · rw [← map_reindex_restrictFace, hPf, Option.map_some, hRp]
      · exact Function.Embedding.ext fun i ↦ congrArg f (G.symm_apply_apply i).symm
    have hgR : univ.map g ∈ R.toCellScheme.faces := ((restrictFace_eq_some_iff R g).mp hRg).1
    have hplan := R.isWellFormed.isWellFormed.isPlan
    rw [R.isWellFormed.ground_eq] at hplan
    have hne : univ.map g ≠ univ := fun he ↦ hsurj fun y ↦ by
      have hy : y ∈ univ.map g := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxR⟩ := hplan.exists_insert_mem hgR hne
    have hx' : x ∉ Set.range g := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set g' := Fin.Embedding.snoc g hx'
    have hgg' : Fin.castSuccEmb.trans g' = g := Fin.Embedding.init_snoc g hx'
    have hg'R : univ.map g' ∈ R.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    have hRg' : restrictFace g' R = some (R.comap g' hg'R) := restrictFace_of_mem R g' hg'R
    have hp'p : restrictFace Fin.castSuccEmb (R.comap g' hg'R) = some p := by
      rw [restrictFace_trans R g' _ hRg', hgg', hRg]
    obtain ⟨P', hP', hP'P, hP'f⟩ := exists_stronglyCoded_pinned_extension hext hP hPf
      ⟨hR.1.restrictFace g' hRg', isStronglyCoded_of_restrictFace hRg' hR.2⟩ hp'p
    have hmk : m < k := by
      have hle : m ≤ k := by simpa using Fintype.card_le_of_embedding g
      refine lt_of_le_of_ne hle fun he ↦ hsurj ?_
      exact ((Fintype.bijective_iff_injective_and_card g).mpr ⟨g.injective, by simp [he]⟩).2
    obtain ⟨N, Q, i', j, hQ, hQP', hQR, hij⟩ :=
      ih (k - (m + 1)) (by omega) hP' hP'f hRg' rfl
    refine ⟨N, Q, Fin.castSuccEmb.trans i', j, hQ, ?_, hQR, ?_⟩
    · rw [← restrictFace_trans Q i' _ hQP', hP'P]
    · have h := congrArg (Fin.castSuccEmb.trans ·) hij
      rw [← Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc,
        castSuccEmb_trans_extendByLast, hgg'] at h
      rw [← h, Function.Embedding.trans_assoc]

/-- **Amalgamation within the strongly coded legal stage types at every stage that is zero or a
limit**: two strongly coded legal stage types with the same face along `f` and `g` are the faces,
along embeddings `i` and `j` with `i ∘ f = j ∘ g`, of one strongly coded legal stage type. -/
theorem exists_stronglyCoded_amalgam_of_isSuccPrelimit (hα : Order.IsSuccPrelimit α)
    {P : StageType.{u} α n} {R : StageType.{u} α k} (hP : P.IsStronglyCodedLegal)
    (hR : R.IsStronglyCodedLegal) {f : Fin m ↪ Fin n} {g : Fin m ↪ Fin k}
    {p : StageType.{u} α m} (hPf : restrictFace f P = some p) (hRg : restrictFace g R = some p) :
    ∃ (N : ℕ) (Q : StageType.{u} α N) (i : Fin n ↪ Fin N) (j : Fin k ↪ Fin N),
      Q.IsStronglyCodedLegal ∧ restrictFace i Q = some P ∧ restrictFace j Q = some R ∧
      f.trans i = g.trans j :=
  exists_stronglyCoded_amalgam (hasStronglyCodedApexCoatomExtensions hα) hP hR hPf hRg

/-- **Joint embedding within the strongly coded legal stage types at every stage that is zero or a
limit**: any two strongly coded legal stage types are faces of one, the amalgam over their faces
on no points. -/
theorem exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit (hα : Order.IsSuccPrelimit α)
    {P : StageType.{u} α n} {R : StageType.{u} α k} (hP : P.IsStronglyCodedLegal)
    (hR : R.IsStronglyCodedLegal) :
    ∃ (N : ℕ) (Q : StageType.{u} α N) (i : Fin n ↪ Fin N) (j : Fin k ↪ Fin N),
      Q.IsStronglyCodedLegal ∧ restrictFace i Q = some P ∧ restrictFace j Q = some R := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (R.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin k))
  obtain ⟨N, Q, i, j, hQ, hQP, hQR, -⟩ := exists_stronglyCoded_amalgam_of_isSuccPrelimit hα hP hR
    hp (hr.trans (congrArg some (eq_of_zero r p)))
  exact ⟨N, Q, i, j, hQ, hQP, hQR⟩

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.LevelZero

/-!
# From a lift in `K₀[L]` to a model of `σ[L]`

Numbering as in the current draft of [AFK26].  The base reduct `G↾L_c[L]` of a structure
`G ∈ K₀[L]` satisfies `σ[L]` (`isTemplateSentenceModel_baseReduct`), clause by clause:

* `Th_Geo` [AFK26, Definition 2.1] is the first clause of the structured geometry of `G`;
* (Singletons), (Convexity) and (Extreme Points) [AFK26, Definition 4.13] hold because the closed
  subtuples of a tuple `w` with invariant `Q_c` are the faces of the plan of the chosen
  representative of `c` (`closedRel_comp_iff`, from the pairs of `ID[L]` and
  `TemplateClass.holds_closed_iff`), and that plan is a plan of [AFK26, Definition 4.1]
  (`StageType.isPlan`): singletons are closed, every closed set with at least two points has
  exactly two extreme points, and anti-exchange holds.  For (Convexity) the two finite sets
  witnessing `y ∈ cl(x̄ ∪ {z})` and `z ∈ cl(x̄ ∪ {y})` are intersected, which is closed by the
  third clause of `Th_Geo`, and both memberships become hull memberships in its plan
  (`mem_hull_of_inClosure`);
* clauses (b) and (c) of [AFK26, Definition 4.22] are the structured geometry and the pairs of
  `ID[L]`, read through `R_c ↔ Q_c` for `c` of rank zero (`relMap_base_iff_invariant`);
* clause (d) is rank-zero density (`density_baseReduct_iff`), a specialization of `D[k]` for the
  finite cutoffs `k < ω = blockStage 0` (`SatisfiesDensityAt.rankZero`).

No countability and no nonemptiness is used.  Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal Finset

noncomputable section

/-! ### Closed subtuples and faces -/

/-- **`P_k` in the template of a class**: `P_k` holds along `i` exactly when `i` is injective and
its image is a face of the plan of the chosen representative.
Correspondence with the printed definitions. -/
theorem TemplateClass.holds_closed_iff {n k : ℕ} (c : TemplateClass.{u} ω₁ n) (hk : 0 < k)
    (i : Fin k → Fin n) :
    c.Holds (TemplateSymbol.closed hk) i ↔
      ∃ h : Function.Injective i, univ.map ⟨i, h⟩ ∈ (Quotient.out c).toCellScheme.faces := by
  have hc : c = (Quotient.out c).toClass := (Quotient.out_eq c).symm
  refine exists_congr fun h ↦ ?_
  rw [← StageType.isSome_restrictFace_iff, Option.isSome_iff_exists]
  constructor
  · rintro ⟨s, hs, -⟩
    rw [hc, TemplateClass.restrictFace_toClass] at hs
    obtain ⟨s', hs', -⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨s', hs'⟩
  · rintro ⟨s', hs'⟩
    refine ⟨s'.toClass, ?_, trivial⟩
    rw [hc, TemplateClass.restrictFace_toClass, hs', Option.map_some]

/-- The image of `Fin.succAbove j` is everything but `j`.  Native construction. -/
theorem Fin.map_succAboveEmb_univ {m : ℕ} (j : Fin (m + 1)) :
    univ.map (Fin.succAboveEmb j) = univ.erase j := by
  conv_rhs => rw [Fin.univ_succAbove m j]
  exact (Finset.erase_cons _).symm

/-- Every nonempty finite set of positions is the image of an embedding of some `Fin (k + 1)`.
Native construction. -/
theorem exists_embedding_univ_map_eq {N : ℕ} (D : Finset (Fin N)) (hD : D.Nonempty) :
    ∃ (k : ℕ) (e : Fin (k + 1) ↪ Fin N), univ.map e = D := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (Finset.card_pos.mpr hD).ne'
  refine ⟨k, (D.orderEmbOfFin hk).toEmbedding, Finset.coe_injective ?_⟩
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
  exact D.range_orderEmbOfFin hk

section Hull

variable {M : Type v} [baseTemplateLanguage.{u}.Structure M]

/-- **A closure membership becomes a hull membership**: let `w` be a tuple whose subtuples on
`k + 1` places satisfy `P` exactly at the faces of a plan `F`.  If `a ∈ cl({b_r})` is witnessed by
a closed tuple `e` containing every point of `w`, and the `b_r` and `a` are points of `w` at the
positions `S` and `pa`, then `pa` lies in the hull of `S` in `F`.
Correspondence with the printed definitions. -/
theorem mem_hull_of_inClosure {N : ℕ} {w : Fin N → M} (hw : Function.Injective w)
    {F : Finset (Finset (Fin N))}
    (key : ∀ (k : ℕ) (e : Fin (k + 1) ↪ Fin N), ClosedRel.{u} k.succ_pos (w ∘ e) ↔ univ.map e ∈ F)
    {ι : Type} {b : ι → M} {a : M} {m : ℕ} {e' : Fin (m + 1) → M}
    (hall : ∀ (k : ℕ) (i : Fin (k + 1) → Fin (m + 1)), ClosedRel.{u} k.succ_pos (e' ∘ i) →
      (∀ r, b r ∈ Set.range (e' ∘ i)) → a ∈ Set.range (e' ∘ i))
    (hsub : ∀ l, w l ∈ Set.range e') {S : Finset (Fin N)} (hSne : S.Nonempty)
    (hS : ∀ r, ∃ s ∈ S, w s = b r) {pa : Fin N} (hpa : w pa = a) :
    pa ∈ Geometry.hull univ F S := by
  rw [Geometry.mem_hull]
  refine ⟨mem_univ _, fun D hD hSD ↦ ?_⟩
  obtain ⟨k, e, he⟩ := exists_embedding_univ_map_eq D (hSne.mono hSD)
  choose j hj using fun l ↦ hsub (e l)
  have hej : e' ∘ j = w ∘ e := funext hj
  have hrange : ∀ q, q ∈ Set.range (w ∘ e) ↔ ∃ d ∈ D, w d = q := fun q ↦ by
    rw [← he]
    simp only [Set.mem_range, Function.comp_apply, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨fun ⟨l, hl⟩ ↦ ⟨e l, ⟨l, rfl⟩, hl⟩, fun ⟨_, ⟨l, rfl⟩, hl⟩ ↦ ⟨l, hl⟩⟩
  have ha := hall k j (by rw [hej, key, he]; exact hD) fun r ↦ by
    rw [hej, hrange]
    obtain ⟨s, hs, hsb⟩ := hS r
    exact ⟨s, hSD hs, hsb⟩
  rw [hej, hrange] at ha
  obtain ⟨d, hd, hda⟩ := ha
  rwa [← hw (hda.trans hpa.symm)]

end Hull

/-! ### The base reduct of a structure of `K₀[L]` -/

variable {M : Type v} {G : templateLanguage.{u}.Structure M}

/-- **Closed subtuples are faces**: if `Q_c(w)`, then `P(w ∘ i)` holds exactly when `i` is
injective with image a face of the plan of the chosen representative of `c`.
Correspondence with the printed definitions. -/
theorem closedRel_comp_iff (hG : IsTemplateCompatible G) {N : ℕ} (hN : 0 < N)
    {c : LegalClass.{u} N} {w : Fin N → M}
    (hw : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hN) w)
    {k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) :
    RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hk) (w ∘ i) ↔
      ∃ h : Function.Injective i, univ.map ⟨i, h⟩ ∈ (Quotient.out c.1).toCellScheme.faces :=
  (hG.relMap_comp_iff hw _ i).trans (c.1.holds_closed_iff hk i)

private theorem injective_of_pairwise {n : ℕ} {x : Fin n → M}
    (h : ∀ i j, i < j → x i ≠ x j) : Function.Injective x := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h i j hlt hij
  · exact h j i hlt hij.symm

/-- **(Convexity) in the base reduct of a compatible structure.**
Correspondence with the printed definitions. -/
theorem convexity_baseReduct (hG : IsTemplateCompatible G) (n : ℕ) (x : Fin (n + 1) → M)
    (y z : M) (hx : @ClosedRel.{u} _ (baseReduct G) _ n.succ_pos x) (hyz : y ≠ z)
    (hxyz : ∀ i, x i ≠ y ∧ x i ≠ z)
    (h1 : @InClosure.{u} _ (baseReduct G) _ y (fun o : Option (Fin (n + 1)) ↦ o.elim z x)) :
    ¬ @InClosure.{u} _ (baseReduct G) _ z (fun o : Option (Fin (n + 1)) ↦ o.elim y x) := by
  classical
  let := baseReduct G
  intro h2
  have geo := hG.isStructuredGeometry.isGeometry
  obtain ⟨m₁, e₁, hb₁, hy₁, hP₁, hall₁⟩ := h1
  obtain ⟨m₂, e₂, hb₂, hz₂, hP₂, hall₂⟩ := h2
  set C : Finset M := univ.image e₁ ∩ univ.image e₂ with hCdef
  have memC : ∀ a, a ∈ C ↔ a ∈ Set.range e₁ ∧ a ∈ Set.range e₂ := fun a ↦ by simp [C]
  have hzC : z ∈ C := (memC z).2 ⟨hb₁ none, hz₂⟩
  have hyC : y ∈ C := (memC y).2 ⟨hy₁, hb₂ none⟩
  have hxC : ∀ i, x i ∈ C := fun i ↦ (memC _).2 ⟨hb₁ (some i), hb₂ (some i)⟩
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨z, hzC⟩
  let w : Fin C.card → M := fun j ↦ (C.equivFin.symm j).1
  have hw : Function.Injective w := fun a b h ↦ C.equivFin.symm.injective (Subtype.ext h)
  have hwC : ∀ a ∈ C, ∃ j, w j = a := fun a ha ↦ ⟨C.equivFin ⟨a, ha⟩, by simp [w]⟩
  have hrange : Set.range w = Set.range e₁ ∩ Set.range e₂ := by
    ext a
    refine ⟨fun ⟨j, hj⟩ ↦ hj ▸ (memC _).1 (C.equivFin.symm j).2, fun ha ↦ hwC a ((memC a).2 ha)⟩
  have hPw : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hCpos) w :=
    geo.inter m₁.succ_pos m₂.succ_pos hCpos e₁ e₂ w hP₁ hP₂ hw hrange
  obtain ⟨Q, hQ, hQw⟩ := (hG.isStructuredGeometry.closed_iff hCpos w).mp hPw
  obtain ⟨c, hN, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
  have hplan := (Quotient.out c.1).isPlan
  have key : ∀ (k : ℕ) (e : Fin (k + 1) ↪ Fin C.card),
      ClosedRel.{u} k.succ_pos (w ∘ e) ↔ univ.map e ∈ (Quotient.out c.1).toCellScheme.faces :=
    fun k e ↦ (closedRel_comp_iff hG hN hQw k.succ_pos e).trans
      ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨e.injective, h⟩⟩
  obtain ⟨py, hpy⟩ := hwC y hyC
  obtain ⟨pz, hpz⟩ := hwC z hzC
  choose ix hix using fun i ↦ hwC (x i) (hxC i)
  have hxinj : Function.Injective x := geo.injective _ x hx
  have hixinj : Function.Injective ix := fun i j h ↦ hxinj (by rw [← hix i, ← hix j, h])
  set B : Finset (Fin C.card) := univ.map ⟨ix, hixinj⟩ with hBdef
  have hwix : w ∘ ix = x := funext hix
  have hB : B ∈ (Quotient.out c.1).toCellScheme.faces := by
    obtain ⟨_, h⟩ := (closedRel_comp_iff hG hN hQw n.succ_pos ix).mp (by rw [hwix]; exact hx)
    exact h
  have hpyB : py ∉ B := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
    exact (hxyz i).1 (by rw [← hix i, ← hpy]; exact congrArg w hi)
  have hpzB : pz ∉ B := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
    exact (hxyz i).2 (by rw [← hix i, ← hpz]; exact congrArg w hi)
  have hpypz : py ≠ pz := fun h ↦ hyz (by rw [← hpy, ← hpz, h])
  have hS (p : Fin C.card) (q : M) (hpq : w p = q) :
      ∀ r : Option (Fin (n + 1)), ∃ s ∈ insert p B, w s = r.elim q x := fun r ↦ by
    cases r with
    | none => exact ⟨p, mem_insert_self _ _, hpq⟩
    | some i => exact ⟨ix i, mem_insert_of_mem (Finset.mem_map_of_mem _ (mem_univ i)), hix i⟩
  have hull₁ := mem_hull_of_inClosure hw key hall₁
    (fun l ↦ (hrange ▸ Set.mem_range_self l : w l ∈ Set.range e₁ ∩ Set.range e₂).1)
    (insert_nonempty _ _) (hS pz z hpz) hpy
  have hull₂ := mem_hull_of_inClosure hw key hall₂
    (fun l ↦ (hrange ▸ Set.mem_range_self l : w l ∈ Set.range e₁ ∩ Set.range e₂).2)
    (insert_nonempty _ _) (hS py y hpy) hpz
  exact hplan.isConvexGeometry.antiExchange hB hpypz hpyB hull₁ hull₂

/-- **The base reduct of a compatible structure fixed by `τ₀` with `D[k]` for every `k ∈ ω`
satisfies `σ[L]`.**  Correspondence with the printed definitions. -/
theorem isTemplateSentenceModel_baseReduct (hG : IsTemplateCompatible G)
    (hfix : projectStructure 0 G = G) (hden : ∀ k : ℕ, SatisfiesDensityAt (k : Ordinal.{u}) G) :
    @IsTemplateSentenceModel.{u} M (baseReduct G) := by
  let := baseReduct G
  have geo := hG.isStructuredGeometry.isGeometry
  have sg := hG.isStructuredGeometry
  refine
    { distinct := fun n x hx i j hij ↦ (geo.injective _ x hx).ne hij.ne
      perm := fun n x σ ↦ geo.perm _ x σ
      extension := fun n x hx ↦ ?_
      inter := fun n₀ n₁ k x y z hx hy hz hzxy hxyz ↦ ?_
      singletons := fun x ↦ ?_
      convexity := convexity_baseReduct hG
      extremePoints := fun m x hx ↦ ?_
      extremePointsExclusion := fun m x hx ↦ ?_
      typing := fun n x ↦ ?_
      exclusive := fun n t t' hne x hx hx' ↦ ?_
      determines := fun n t k S i x y hx hy ↦ ?_
      diagram := fun n t x hx k S i ↦ ?_
      density := (density_baseReduct_iff hG hfix).mpr fun k ↦ (hden k).rankZero }
  · obtain ⟨k, y, hy, hP⟩ := geo.exists_closed n.succ_pos x (injective_of_pairwise hx)
    refine ⟨k, y ∘ Fin.natAdd (n + 1), ?_⟩
    subst hy
    have hyy : Fin.append (y ∘ Fin.castAdd k) (y ∘ Fin.natAdd (n + 1)) = y :=
      Fin.append_castAdd_natAdd
    rw [hyy]
    exact hP
  · refine geo.inter _ _ _ x y z hx hy (injective_of_pairwise hz) (Set.ext fun a ↦ ?_)
    constructor
    · rintro ⟨l, rfl⟩
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hzxy l
      exact ⟨⟨i, hi.symm⟩, ⟨j, hj.symm⟩⟩
    · rintro ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
      obtain ⟨l, hl⟩ := hxyz i j hj.symm
      exact ⟨l, hl.symm⟩
  · obtain ⟨N, hN, c, y, i, hy, hyi⟩ := exists_relMap_invariant_comp hG Nat.one_pos ![x]
    rw [← hyi]
    have hi : Function.Injective i := fun a b _ ↦ Subsingleton.elim a b
    refine (closedRel_comp_iff hG hN hy Nat.one_pos i).mpr ⟨hi, ?_⟩
    have : univ.map ⟨i, hi⟩ = {i 0} := by
      ext a
      simp only [Finset.mem_map, mem_univ, true_and, Finset.mem_singleton,
        Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨b, hb⟩ ↦ by rw [← hb, Subsingleton.elim b 0], fun h ↦ ⟨0, h.symm⟩⟩
    rw [this]
    exact (Quotient.out c.1).isPlan.singleton_mem (mem_univ _)
  · obtain ⟨Q, hQ, hQx⟩ := (sg.closed_iff _ x).mp hx
    obtain ⟨c, hN, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
    have hplan := (Quotient.out c.1).isPlan
    have hext : ∀ j : Fin (m + 3), ClosedRel.{u} (k := m + 2) (by omega) (x ∘ j.succAbove) ↔
        j ∈ Geometry.extremes (Quotient.out c.1).toCellScheme.faces univ := fun j ↦
      (closedRel_comp_iff hG hN hQx (by omega) _).trans (by
        rw [Geometry.mem_extremes, ← Fin.map_succAboveEmb_univ]
        exact ⟨fun ⟨_, h⟩ ↦ ⟨mem_univ _, h⟩, fun ⟨_, h⟩ ↦ ⟨(Fin.succAboveEmb j).injective, h⟩⟩)
    obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.mp
      (hplan.card_extremes hplan.ground_mem (by simp))
    have ha : a ∈ Geometry.extremes (Quotient.out c.1).toCellScheme.faces univ := by simp [hE]
    have hb : b ∈ Geometry.extremes (Quotient.out c.1).toCellScheme.faces univ := by simp [hE]
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, (hext a).mpr ha, (hext b).mpr hb⟩
    · exact ⟨b, a, h, (hext b).mpr hb, (hext a).mpr ha⟩
  · obtain ⟨Q, hQ, hQx⟩ := (sg.closed_iff _ x).mp hx
    obtain ⟨c, hN, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
    have hplan := (Quotient.out c.1).isPlan
    have hext : ∀ j : Fin (m + 3), ClosedRel.{u} (k := m + 2) (by omega) (x ∘ j.succAbove) ↔
        j ∈ Geometry.extremes (Quotient.out c.1).toCellScheme.faces univ := fun j ↦
      (closedRel_comp_iff hG hN hQx (by omega) _).trans (by
        rw [Geometry.mem_extremes, ← Fin.map_succAboveEmb_univ]
        exact ⟨fun ⟨_, h⟩ ↦ ⟨mem_univ _, h⟩, fun ⟨_, h⟩ ↦ ⟨(Fin.succAboveEmb j).injective, h⟩⟩)
    rintro ⟨h0, h1, h2⟩
    have hsub : ({0, 1, 2} : Finset (Fin (m + 3))) ⊆
        Geometry.extremes (Quotient.out c.1).toCellScheme.faces univ := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact (hext 0).mp h0
      · exact (hext 1).mp h1
      · exact (hext 2).mp h2
    have h3 : ({0, 1, 2} : Finset (Fin (m + 3))).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, 1, 2, by simp,
        by simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)],
        by simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)], rfl⟩
    have := (Finset.card_le_card hsub).trans (hplan.card_extremes_le_two hplan.ground_mem)
    omega
  · change RelMap (L := templateLanguage.{u}) (self := G) _ _ ↔ _
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := (sg.closed_iff _ x).mp hx
      obtain ⟨c, hN, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
      have h0 := fixed_of_relMap_invariant hfix hQx
      exact ⟨⟨c, h0⟩, (relMap_base_iff_invariant hG hfix c h0 _ x).mpr hQx⟩
    · rintro ⟨t, ht⟩
      exact (sg.closed_iff _ x).mpr ⟨TemplateSymbol.invariant t.1 n.succ_pos, trivial,
        (relMap_base_iff_invariant hG hfix _ t.2 _ x).mp ht⟩
  · refine sg.exclusive (TemplateSymbol.invariant t.1 n.succ_pos)
      (TemplateSymbol.invariant t'.1 n.succ_pos) trivial trivial (fun h ↦ hne ?_) x
      ((relMap_base_iff_invariant hG hfix _ t.2 _ x).mp hx)
      ((relMap_base_iff_invariant hG hfix _ t'.2 _ x).mp hx')
    exact Subtype.ext (TemplateSymbol.invariant.inj h)
  · exact sg.determines (TemplateSymbol.invariant t.1 n.succ_pos) S.toTemplateSymbol i trivial x y
      ((relMap_base_iff_invariant hG hfix _ t.2 _ x).mp hx)
      ((relMap_base_iff_invariant hG hfix _ t.2 _ y).mp hy)
  · exact hG.relMap_comp_iff ((relMap_base_iff_invariant hG hfix _ t.2 _ x).mp hx) _ i

end

end VaughtConjecture

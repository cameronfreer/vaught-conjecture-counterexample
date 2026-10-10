/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem
import VaughtConjecture.Continuation.GrowthExactCarrier

/-!
# Legal growth carriers with literal faces exist

Roadmap, Layer 3 (the growth carrier, its legality).  Every legal one-point extension `Q` of a
context `P` with face `d` along `extendByLast e` is a growth carrier for the schemes of `P` and
`d` along `e`, with **literal** context and donor faces (`GrowthCarrier.ofExtension`).  By the
exact pinned extension at a stage that is zero or a limit
(`StageType.exists_pinned_extension_of_isSuccPrelimit`) such an extension exists for every legal
context, every closed face of it and every legal one-point coface of that face
(`GrowthCarrier.nonempty_of_isSuccPrelimit`).

At the root cells the recovery holds for every carrier (`GrowthCarrier.recovers_root`): the
context and donor faces meet literally in the root face; so exact recovery is recovery at the
donor cells whose scope contains the new point (`GrowthCarrier.recovers_eq_of_recovers_new`).

So legality of a growth carrier with literal faces is never the obstacle: what the finite carrier
statements `StageType.HasExactGrowthCarriers` and `StageType.HasStableGrowthCarriers` ask beyond
this is the **recovery** (`GrowthCarrier.Recovers`), for every lawful section of the carrier's rows.
A pinned extension recovers nothing in general; the recovery is the content of the construction of
the carrier: compiled for the margin calibration and for the hollow reference calibration with a
nonempty root from `StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed), open
for the other calibrations.

## References

The coatom extension property and the pinned extension are [Kni26, Lemma 4.4.1] and its proof.
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ}

/-- **A legal one-point extension is a growth carrier**: a legal `Q` on `J + 1` points with face
`P` along the first points and face `d` along `extendByLast e` is a growth carrier for the schemes
of `P` and `d`, with those faces literally. -/
def ofExtension {Q : StageType.{u} α (J + 1)} (hQ : Q.IsLegal) {P : StageType.{u} α J}
    (hP : restrictFace Fin.castSuccEmb Q = some P) {e : Fin n ↪ Fin J}
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast e) Q = some d) :
    GrowthCarrier P.toScheme d.toScheme e where
  scheme := Q.toScheme
  isLegal := hQ
  context_mem := ((restrictFace_eq_some_iff Q _).mp hP).1
  comap_context := congrArg StageType.toScheme ((restrictFace_eq_some_iff Q _).mp hP).2
  donor_mem := ((restrictFace_eq_some_iff Q _).mp hd).1
  comap_donor := congrArg StageType.toScheme ((restrictFace_eq_some_iff Q _).mp hd).2

/-- The scheme of the carrier of an extension is the scheme of the extension. -/
@[simp] theorem ofExtension_scheme {Q : StageType.{u} α (J + 1)} (hQ : Q.IsLegal)
    {P : StageType.{u} α J} (hP : restrictFace Fin.castSuccEmb Q = some P) {e : Fin n ↪ Fin J}
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast e) Q = some d) :
    (ofExtension hQ hP hd).scheme = Q.toScheme :=
  rfl

/-- **Legal growth carriers with literal faces exist** at every stage that is zero or a limit:
for a legal context `P`, a closed face `e` of it with restriction `p`, and a legal one-point
coface `d` of `p`, some growth carrier has the scheme of `P` as its context face and the scheme
of `d` as its donor face. -/
theorem nonempty_of_isSuccPrelimit (hα : Order.IsSuccPrelimit α) {P : StageType.{u} α J}
    (hP : P.IsLegal) {e : Fin n ↪ Fin J} {p : StageType.{u} α n} (hPe : restrictFace e P = some p)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ p.cofaces) :
    Nonempty (GrowthCarrier P.toScheme d.toScheme e) := by
  obtain ⟨Q, hQ, hQP, hQd⟩ := exists_pinned_extension_of_isSuccPrelimit hα hP hPe hd.1 hd.2
  exact ⟨ofExtension hQ hQP hQd⟩

/-! ### Recovery at the root cells -/

/-- Cell maps of equal schemes agree, as positions, at equal positions. -/
theorem _root_.VaughtConjecture.Scheme.val_cellMap_congr {m k : ℕ} {S S' : Scheme.{u} m}
    (hS : S = S') (f : Fin k ↪ Fin m) {a : Fin (S.comap f).card} {b : Fin (S'.comap f).card}
    (hab : (a : ℕ) = b) : (S.cellMap f a : ℕ) = S'.cellMap f b := by
  subst hS
  rw [Fin.ext hab]

/-- **Recovery at the root cells, for every carrier**: let the context `t'` restrict along `e` to
`p`, and the donor `d` restrict to `p` along the first points.  Every lawful section of a growth
carrier that is the labelling of `t'` on the context face is the labelling of `d` at the cells of
the donor face whose scope lies in the root: the context and donor faces of the carrier meet in
the root face, literally.  So the recovery asked of a carrier is only at the donor cells whose
scope contains the new point. -/
theorem recovers_root {t' : StageType.{u} α J} {e : Fin n ↪ Fin J} {p : StageType.{u} α n}
    (hte : restrictFace e t' = some p) {d : StageType.{u} α (n + 1)}
    (hdp : restrictFace Fin.castSuccEmb d = some p)
    (G : GrowthCarrier t'.toScheme d.toScheme e) :
    G.Recovers t'.label fun j ℓ ↦ j ∈ d.visibleCells Fin.castSuccEmb → ℓ = d.label j := by
  intro v _ hctx i j hij hj
  obtain ⟨hfe, hpe⟩ := (restrictFace_eq_some_iff t' e).mp hte
  obtain ⟨hfd, hpd⟩ := (restrictFace_eq_some_iff d _).mp hdp
  -- the donor cell is a root cell of `d`
  have hj' : j ∈ Set.range (d.cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact hj
  obtain ⟨i₁, rfl⟩ := hj'
  have hD : G.scheme.comap (extendByLast e) = d.toScheme := G.comap_donor
  have hC : G.scheme.comap Fin.castSuccEmb = t'.toScheme := G.comap_context
  have hc₁ : ((G.scheme.comap (extendByLast e)).comap Fin.castSuccEmb).card =
      (d.toScheme.comap Fin.castSuccEmb).card := by rw [hD]
  let i₁' : Fin ((G.scheme.comap (extendByLast e)).comap Fin.castSuccEmb).card :=
    Fin.cast hc₁.symm i₁
  -- the position of the donor cell in the donor face
  have hi : i = (G.scheme.comap (extendByLast e)).cellMap Fin.castSuccEmb i₁' :=
    Fin.ext (hij.trans (Scheme.val_cellMap_congr hD.symm _ (a := i₁) (b := i₁') rfl))
  have hc₂ : ((G.scheme.comap (extendByLast e)).comap Fin.castSuccEmb).card =
      (G.scheme.comap (Fin.castSuccEmb.trans (extendByLast e))).card := by rw [Scheme.comap_comap]
  have hc₃ : (G.scheme.comap (Fin.castSuccEmb.trans (extendByLast e))).card =
      (G.scheme.comap (e.trans Fin.castSuccEmb)).card := by rw [castSuccEmb_trans_extendByLast]
  have hc₄ : ((G.scheme.comap Fin.castSuccEmb).comap e).card =
      (G.scheme.comap (e.trans Fin.castSuccEmb)).card := by rw [Scheme.comap_comap]
  let i₄ : Fin ((G.scheme.comap Fin.castSuccEmb).comap e).card :=
    Fin.cast (hc₂.trans (hc₃.trans hc₄.symm)) i₁'
  have hcell : G.scheme.cellMap (extendByLast e) i =
      G.scheme.cellMap Fin.castSuccEmb ((G.scheme.comap Fin.castSuccEmb).cellMap e i₄) := by
    rw [hi, G.scheme.cellMap_cellMap _ _ (j := Fin.cast hc₂ i₁') rfl,
      G.scheme.cellMap_congr (castSuccEmb_trans_extendByLast e)
        (j := Fin.cast (hc₂.trans hc₃) i₁') rfl,
      G.scheme.cellMap_cellMap _ _ (i := i₄) (j := Fin.cast (hc₂.trans hc₃) i₁') rfl]
  have hc₅ : ((G.scheme.comap Fin.castSuccEmb).comap e).card = (t'.toScheme.comap e).card := by
    rw [hC]
  let k₅ : Fin t'.card :=
    Fin.cast (congrArg Scheme.card hC) ((G.scheme.comap Fin.castSuccEmb).cellMap e i₄)
  rw [hcell, hctx _ k₅ rfl]
  -- both labels are the label of `p` at the same position
  have h₁ : t'.label k₅ = t'.label (t'.cellMap e (Fin.cast hc₅ i₄)) :=
    congrArg t'.label
      (Fin.ext (Scheme.val_cellMap_congr hC _ (a := i₄) (b := Fin.cast hc₅ i₄) rfl))
  rw [h₁]
  have hp1 : (d.comap Fin.castSuccEmb hfd).card = p.card := by rw [hpd]
  exact (StageType.label_congr hpe (j := Fin.cast hp1 i₁) rfl).trans
    (StageType.label_congr hpd.symm (j := i₁) rfl)

/-- **Exact recovery is recovery at the new cells**: a growth carrier recovers the labels of `d`
exactly from the labels of `t'` as soon as it does so at the donor cells whose scope is not in
the root (`recovers_root` gives the others). -/
theorem recovers_eq_of_recovers_new {t' : StageType.{u} α J} {e : Fin n ↪ Fin J}
    {p : StageType.{u} α n} (hte : restrictFace e t' = some p) {d : StageType.{u} α (n + 1)}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (G : GrowthCarrier t'.toScheme d.toScheme e)
    (hnew : G.Recovers t'.label
      fun j ℓ ↦ j ∉ d.visibleCells Fin.castSuccEmb → ℓ = d.label j) :
    G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j := fun v hv hctx i j hij ↦ by
  by_cases hj : j ∈ d.visibleCells Fin.castSuccEmb
  · exact recovers_root hte hdp G v hv hctx i j hij hj
  · exact hnew v hv hctx i j hij hj

end GrowthCarrier

namespace StageType

/-- **Exact growth carriers at the new cells**, the part of `StageType.HasExactGrowthCarriers` not
given by `GrowthCarrier.recovers_root` (open): over every calibrated legal context, some growth
carrier, with literal context and donor faces, recovers the labels of `d` from the labels of `t'`
at every donor cell whose scope is not in the root. -/
def HasExactGrowthCarriersAtNewCells
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ t : StageType.{u} α n, restrictFace h t' = some t →
      ∀ d ∈ t.cofaces, C t' h d → ∃ G : GrowthCarrier t'.toScheme d.toScheme h,
        G.Recovers t'.label fun j ℓ ↦ j ∉ d.visibleCells Fin.castSuccEmb → ℓ = d.label j

/-- Exact growth carriers at the new cells are exact growth carriers
(`GrowthCarrier.recovers_eq_of_recovers_new`). -/
theorem HasExactGrowthCarriersAtNewCells.hasExactGrowthCarriers
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (h : HasExactGrowthCarriersAtNewCells C) : HasExactGrowthCarriers C :=
  fun _ _ _ t' g hα ht' t ht d hd hC ↦
    let ⟨G, hG⟩ := h t' g hα ht' t ht d hd hC
    ⟨G, G.recovers_eq_of_recovers_new ht hd.2 hG⟩

end StageType

end VaughtConjecture

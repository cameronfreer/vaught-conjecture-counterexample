/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedAssembly
import VaughtConjecture.Extension.ReplicatedRendering

/-!
# Cap-compatible rendering at the choice of height, values and grid bound

Roadmap, Layer 3 ((R3) and (R4), the rendering of states in the replicated scheme).

The statement `Seed.CapCompatibleRendering` at the choice of the seed position
(`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`) with the admission predicate of the
requests (`Seed.attachAdmits`): `Seed.CapCompatibleRenderingAtChoice`.  Both failing families of
`VaughtConjecture.Extension.ReplicatedRendering` are stated at this choice with only the states
left as hypotheses:

* `Seed.not_capCompatibleRenderingAtChoice_of_split`: the cap `ω * b₀ + F`, with `F` above `k + 2`,
  at least `j`, and above every finite part of the values of the choice in the block `b₀` (such `F`
  exist: `Label.exists_finPart_above`), and two states agreeing capped at it whose smaller value
  at a separating cell is `ω * (b₀ + 1) + f` with `f < k + 2`;
* `Seed.not_capCompatibleRenderingAtChoice_of_collapse`: the cap `ω * b + (j + 1)`, a value of the
  code set (so of the choice) and a height at every grade at most `j + 1`, one state with no value
  of finite part above `j` below it, and a state of the catalogue at `k + 2` agreeing with it
  capped there and separated below it.

## References

Agreement heights are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
  {d : StageType.{u} α (n + 1)}
  (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
  (Q : GrowthRequests I.left d.toScheme)

/-- **Cap-compatible rendering at the choice** of height, values and grid bound, with the
admission predicate of the requests `Q`. -/
abbrev CapCompatibleRenderingAtChoice (j : ℕ) : Prop :=
  I.CapCompatibleRendering g (I.seedHeight g) (I.seedValues g) (I.attachAdmits g hdA Q)
    (I.seedGridBound g) j

variable {I g hdA Q}

/-- **At the choice, the rendering fails at a cap above a block** with no value of the choice
between it and the next block's low values: two states of the catalogue at `m + 2` agreeing capped
at `ω * b₀ + F` and separated at a cell where the smaller value is `ω * (b₀ + 1) + f`, `f < k + 2`,
`k + 2 ≤ j`. -/
theorem not_capCompatibleRenderingAtChoice_of_split {j k : ℕ} (hkj : k + 2 ≤ j)
    (hkm : k + 1 ≤ m) {b₀ F f : ℕ} (hF : ∀ e : ℕ, gridPoint.{u} e b₀ ∈ I.seedValues g → e < F)
    (hFk : k + 2 < F) (hFj : j ≤ F) (hf : f < k + 2) {R R' : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat (I.seedValues g) (I.attachAdmits g hdA Q) (m + 2))
    (hR' : R' ∈ (I.attachmentBase g).towerCat (I.seedValues g) (I.attachAdmits g hdA Q) (m + 2))
    (hag : ∀ a, min (R a) (gridPoint F b₀) = min (R' a) (gridPoint F b₀))
    {a : Fin (I.attachment g).card} (hne : R a ≠ R' a)
    (hmin : min (R a) (R' a) = gridPoint f (b₀ + 1)) :
    ¬ I.CapCompatibleRenderingAtChoice g hdA Q j :=
  not_capCompatibleRendering_of_split (I.card_le_seedHeight g)
    (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx) (I.attachAdmits_succ g hdA Q) hkj hkm
    ((isSelfVisible_gridPoint F b₀).mono hFj) hR hR' hag hne fun _ hx hcx ↦
      hmin ▸ Scheme.lt_of_mem_heightSet_of_cap (fun _ hx ↦ I.lt_omega0_sq_of_mem_seedValues g hx)
        hF hFk hf hx hcx

/-- The cap `ω * b + (j + 1)` is a value of the choice for `b` at most the number of cells and
`j ≤ m + 1`. -/
theorem gridPoint_mem_seedValues {j b : ℕ} (hjm : j ≤ m + 1) (hb : b ≤ (I.attachment g).card) :
    gridPoint.{u} (j + 1) b ∈ I.seedValues g :=
  I.codeSet_subset_seedValues g (mem_codeSet hb (by omega))

/-- The collapse at `j` lowers the cap `ω * b + (j + 1)`. -/
theorem finCollapse_gridPoint_lt (j b : ℕ) : finCollapse j (gridPoint.{u} (j + 1) b) <
    gridPoint (j + 1) b :=
  finCollapse_lt (by rw [finNat_add_natCast (isSuccPrelimit_omega0_mul' _)]; omega)

/-- **At the choice, the rendering fails at a cap that is a height** when the decoders agree only
on the values of the states: the cap `ω * b + (j + 1)`, a state `R` of the catalogue at `m + 2`
whose values are kept by the collapse at `j` capped there, and a state `R''` of the catalogue at
`k + 2 ≤ j` agreeing with `R` capped there and separated from it at a cell where `R''` is at most
the cap. -/
theorem not_capCompatibleRenderingAtChoice_of_collapse {j k : ℕ} (hkj : k + 2 ≤ j)
    (hkm : k + 1 ≤ m) (hjm : j ≤ m + 1) {b : ℕ} (hb : b ≤ (I.attachment g).card)
    {R R'' : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat (I.seedValues g) (I.attachAdmits g hdA Q) (m + 2))
    (hR'' : R'' ∈ (I.attachmentBase g).towerCat (I.seedValues g) (I.attachAdmits g hdA Q) (k + 2))
    (hag : ∀ e, min (R'' e) (gridPoint (j + 1) b) = min (R e) (gridPoint (j + 1) b))
    {a : Fin (I.attachment g).card} (ha : R'' a ≤ gridPoint (j + 1) b) (hlt : R'' a < R a)
    (hfix : ∀ e, min (finCollapse j (R e)) (gridPoint (j + 1) b) =
      min (R e) (gridPoint (j + 1) b)) :
    ¬ I.CapCompatibleRenderingAtChoice g hdA Q j :=
  not_capCompatibleRendering_of_collapse (I.card_le_seedHeight g) hkj hkm
    (gridPoint_mem_seedValues hjm hb) (gridPoint_ne_bot _ _)
    ((isSelfVisible_gridPoint (j + 1) b).mono (by omega)) (finCollapse_gridPoint_lt j b) hR hR''
    hag ha hlt hfix

end Seed

end VaughtConjecture

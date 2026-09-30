/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Function

/-!
# Lifting a face through observation fibres

Roadmap, Layer 0, "Capped extension".  Let `r : Y → X` be a restriction map between two spaces of
lawful sections (a full section restricted to a face), and let `obsX : X → OX`, `obsY : Y → OY` be
observations, for instance at one permitted cap.  The observation spaces `OX`, `OY` are arbitrary
types: an observed value need not be a lawful section, and no cap endomorphism of `X` or `Y` is
assumed.  Nor is `r` assumed injective.

The *observation fibre* of `q` is `obsY ⁻¹' {obsY q}`, the set of sections observed like `q`
(Mathlib's preimage of a singleton; no separate "ball" is defined).  *Lifting at `q`* says that
every face section `p` observed like `r q` is the face of some section observed like `q`:
`∀ p, obsX p = obsX (r q) → ∃ q', r q' = p ∧ obsY q' = obsY q`.

* `Knight.Observation.surjOn_fiber_iff`: lifting at `q` is `Set.SurjOn r` from the observation
  fibre of `q` onto the observation fibre of `r q`.  No hypothesis is needed.
* `Knight.Observation.image_fiber_eq_iff`: if the observations are compatible at `q` (sections
  observed like `q` have faces observed like `r q`, i.e. `Set.MapsTo r` between the two fibres),
  then lifting at `q` is equality of the image of the fibre of `q` with the fibre of `r q`.

Both statements are pointwise in `q`; the global lifting property quantifies them over all
`q`.  The second reduces to the first through Mathlib's `Set.image_eq_iff_surjOn_mapsTo`.
-/

namespace Knight.Observation

open Set

variable {X Y OX OY : Type*} (r : Y → X) (obsX : X → OX) (obsY : Y → OY) (q : Y)

/-- **Lifting is fibre surjectivity.**  Every face section observed like `r q` is the face of a
section observed like `q` iff `r` maps the observation fibre of `q` onto the observation fibre of
`r q`. -/
theorem surjOn_fiber_iff :
    SurjOn r (obsY ⁻¹' {obsY q}) (obsX ⁻¹' {obsX (r q)}) ↔
      ∀ p, obsX p = obsX (r q) → ∃ q', r q' = p ∧ obsY q' = obsY q := by
  simp only [SurjOn, subset_def, mem_preimage, mem_singleton_iff, mem_image]
  exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ exists_congr fun _ ↦ and_comm

/-- **Lifting is fibre image equality under compatibility.**  If every section observed like `q`
has its face observed like `r q`, then every face section observed like `r q` lifts to a section
observed like `q` iff the image under `r` of the observation fibre of `q` is exactly the
observation fibre of `r q`. -/
theorem image_fiber_eq_iff (hcompat : ∀ q', obsY q' = obsY q → obsX (r q') = obsX (r q)) :
    r '' (obsY ⁻¹' {obsY q}) = obsX ⁻¹' {obsX (r q)} ↔
      ∀ p, obsX p = obsX (r q) → ∃ q', r q' = p ∧ obsY q' = obsY q := by
  rw [image_eq_iff_surjOn_mapsTo, surjOn_fiber_iff, and_iff_left_iff_imp]
  exact fun _ q' hq' ↦ hcompat q' hq'

end Knight.Observation

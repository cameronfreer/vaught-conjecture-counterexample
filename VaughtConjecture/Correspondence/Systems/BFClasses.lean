/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.BackAndForth

/-!
# [AFK26, Theorem 2.19] for an arbitrary weak system

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a weak
system `W` (`WeakSystem D S`) and a base sublanguage `E`:

**Occurrence of a fixed invariant**:

* `WeakSystem.exists_relMap_fixed_invariant`: every member `G ∈ K_β` holds an invariant `Q` with
  `τ_β(Q) = Q` of some tuple.  A point of the (nonempty, `WeakSystem.nonempty`) carrier, the
  closure clause of the geometry on the one-point tuple (`IsGeometry.exists_closed`), an invariant
  of the closed tuple (`IsStructuredGeometry.closed_iff`), and `τ_β(G) = G` (`WeakSystem.fixed`):
  the invariant holds in `τ_β(G)`, so it is `τ_β(Q')` for some `Q'`, and `τ_β ∘ τ_β = τ_β`
  (`InvariantSystem.comp`).
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', v} D S)

/-! ### Occurrence of a fixed invariant -/

/-- **Every member of `K_β` holds a `β`-invariant of some tuple**: for `G ∈ K_β` there are an
invariant `Q` with `τ_β(Q) = Q` (a member of the countable set of the field
`InvariantSystem.countable`) and a tuple `a` with `G ⊨ Q(a)`.  A point `p` of the carrier
(`nonempty`); the one-point tuple at `p` extends to a tuple `z` with `P_{1+l}`
(`IsGeometry.exists_closed`), which carries an invariant `P` (`IsStructuredGeometry.closed_iff`);
as `τ_β(G) = G` (`fixed`), `P = τ_β(Q')` for an invariant `Q'` of `G`, and
`τ_β(τ_β(Q')) = τ_β(Q')` (`InvariantSystem.comp`).  Correspondence with the printed
definitions. -/
theorem exists_relMap_fixed_invariant {β : SystemLevel} {M : Type v} {G : L.Structure M}
    (hG : G ∈ W.K β M) :
    ∃ Q : Σ n, σ.Invariant n, S.τ β Q.2 = Q.2 ∧
      ∃ a : Fin Q.1 → M, RelMap (L := L) (self := G) Q.2.1 a := by
  obtain ⟨p⟩ := W.nonempty hG
  have hsG : @IsStructuredGeometry L σ M G := (W.isCompatible hG).1
  obtain ⟨l, z, -, hz⟩ := hsG.isGeometry.exists_closed one_pos (fun _ : Fin 1 ↦ p)
    fun i j _ ↦ Subsingleton.elim i j
  obtain ⟨P, hP, hzP⟩ := (hsG.closed_iff _ z).mp hz
  have hzP' : RelMap (L := L) (self := S.projection β G) P z := by
    rw [W.fixed hG]
    exact hzP
  obtain ⟨Q', hQ', -⟩ := (S.relMap_projection_of_isInvariant β G hP z).mp hzP'
  have hQ : S.τ β Q' = ⟨P, hP⟩ := Subtype.ext hQ'
  refine ⟨⟨1 + l, ⟨P, hP⟩⟩, ?_, z, hzP⟩
  change S.τ β ⟨P, hP⟩ = ⟨P, hP⟩
  rw [← hQ, (S.comp le_rfl Q').1]

end WeakSystem

end VaughtConjecture.Correspondence

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeCode
import VaughtConjecture.Extension.AlignedEncoding

/-!
# The single decoder at a grade and the lawfulness of the codes

Roadmap, Layer 3 ((R3) and (R4), the context lift at an arbitrary grade with the values per
grade): the decoder composing the aligned encoding with the orbit code, and the lawfulness the
rendering asks of the coded state.

Four labels are kept apart: the **ambient label** (the value of the ambient at a cell, read by the
ambient's decoder `τ` from its source `s`), the **coded value** (a value of the source `s` or of
the orbit code `P` of the aligned codes `f`), the **external cap** `c`, and the **source cut**
`h` (a value self-visible and short at the grade, at most the source at the owner).

**The decoder** (`Label.singleDecoder_spec`).  From the data of the aligned encoding
(`CellScheme.Rows.IsLawfulBelow.exists_alignedEncoding`: a witness `ρ` reading the aligned codes
`f` as the prescription, and the cap transport `min (ρ x) c = min (τ z) c` for labels `x`
agreeing capped at `h` with a short `z`) and an orbit-canonical source `s` with `f` agreeing with
`s` capped at `h`, the decoder `σ = ρ ∘ orbitDecoder k f h` of the orbit code `P` of `f`:

* reads `P` literally as the prescription (`Label.orbitDecoder_orbitCode`, then `ρ`);
* agrees with `s` capped at `h` (`Label.min_orbitCode_eq`), so the rendering's common cut is `h`;
* reaches the cap at `h`, as `τ` does: the cap transport at `x = h` and `z` the source at the
  owner, whose ambient reading is the cap (`hface` and `γ < p o` of the alignment);
* agrees with `τ` capped at `c` at every short label `w < h` off the strip of `h`
  (`visibilityReplace k k w < h`): there the orbit decoder is the identity
  (`Label.orbitDecoder_of_visibilityReplace_lt`), and the cap transport applies with `x = z = w`;
* is monotone.

**What fails** (stated, not compiled as a counterexample): (1) on the strip of `h` below `h` the
orbit decoder reads a label at the key `h` of a code as the reading of that cell, which may lie
above `h`; the cut agreement then needs the label to be a code value, read literally, and a
writing value on the strip that is not a code value (the ladder value `1` when `h = 2`) is not
covered.  (2) `ρ ∘ orbitDecoder` is monotone but a witness bounded by `k` only when `ρ` reflects
`⊥` on the decoder's values (`IsWitness.comp_of_bot_reflecting`); the extended decoder of the
aligned encoding is `⊥` below `μ` wherever `min (ρ' x) δ` is, so it does not reflect `⊥` in
general.  The rendering needs only monotone decoders; the lawfulness of the decoded lift needs the
witness.

**Lawfulness of the codes** (`Seed.grade_attachment_le`, `Seed.isLawful_orbitCode_top`,
`Seed.not_isLawful_orbitCode_of_grade_lt`).  The rendering (`Seed.capCompatibleRendering`) asks
both states to be **fully** lawful on the attachment: the extension `stateExt` to the padded base
is defined by cases on full lawfulness (it needs the rank member of the state,
`Scheme.RankMember.ofLawful`), and is `⊥` everywhere otherwise.  Every cell of the attachment has
grade at most `m + 1` (it lies in the context face or the donor face); so at the top grade
`k = m + 1` the orbit code of a fully lawful state is fully lawful.  Below the top grade it is not:
at a cell of grade above `k` where the state is not `⊥`, the orbit code is short at `k`, never the
formal top and not `⊥`, so not self-visible at that grade.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; lawful sections are
[Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

variable {k : ℕ} {ι : Type*} [Fintype ι]

/-- **Off the strip of the cut the orbit decoder is the identity**: a label `x < h` whose key
`visibilityReplace k k x` lies below `h` is read as itself. -/
theorem orbitDecoder_of_visibilityReplace_lt {w : ι → Label.{u}} {h x : Label.{u}}
    (hx : x < h) (hxk : visibilityReplace k k x < h) : orbitDecoder k w h x = x := by
  unfold orbitDecoder
  rw [min_eq_left hx.le]
  refine max_eq_left (Finset.sup_le fun d hd ↦ ?_)
  have hd' : h ≤ visibilityReplace k k (orbitCode k w d) := (Finset.mem_filter.mp hd).2
  unfold cellReading
  rw [ite_eq_left (hxk.trans_le hd')]
  exact bot_le

/-- **The single decoder at the grade `k`.**  Let `ρ` read the aligned codes `f` as the
prescription `pe`, with the cap transport to the ambient's decoder `τ` at the cap `c` through the
cut `h`; let `s` be an orbit-canonical source agreeing with `f` capped at `h`, with a cell `o`
where `h ≤ s o` and `τ` reads the cap.  Then `σ = ρ ∘ orbitDecoder k f h`, on the orbit code `P` of
`f`: reads `P` as `pe`; `P` agrees with `s` capped at `h`; `σ` and `τ` reach `c` at `h`; and `σ`
agrees with `τ` capped at `c` at every short label below `h` off its strip; `σ` is monotone. -/
theorem singleDecoder_spec {f s pe : ι → Label.{u}} {h c : Label.{u}} {ρ τ : Label.{u} → Label.{u}}
    (hρ : IsWitness (stepSuppressor k) ρ) (hh : IsSelfVisible k h)
    (hs : IsShort k h) (h0 : h ≠ ⊥) (hsc : orbitCode k s = s)
    (hfs : ∀ e, min (f e) h = min (s e) h) (hread : ∀ e, ρ (f e) = pe e)
    (hcap : ∀ x z, IsShort k z → min x h = min z h → min (ρ x) c = min (τ z) c) {o : ι}
    (hho : h ≤ s o) (hso : IsShort k (s o)) (hτo : c ≤ τ (s o)) :
    (∀ e, (ρ ∘ orbitDecoder k f h) (orbitCode k f e) = pe e) ∧
      (∀ e, min (orbitCode k f e) h = min (s e) h) ∧
      c ≤ (ρ ∘ orbitDecoder k f h) h ∧ c ≤ τ h ∧
      (∀ w, w < h → visibilityReplace k k w < h → IsShort k w →
        min ((ρ ∘ orbitDecoder k f h) w) c = min (τ w) c) ∧
      Monotone (ρ ∘ orbitDecoder k f h) := by
  obtain ⟨-, -, hP, -, -, -, hθ, hlit⟩ :=
    exists_freshCode_above_cut (B := 2 * Fintype.card ι) le_rfl hsc hh hs h0 hfs
  have hρh : c ≤ ρ h := by
    have e := hcap h (s o) hso (by rw [min_self, min_eq_right hho])
    rw [min_eq_right hτo] at e
    exact e ▸ min_le_left _ _
  have hτh : c ≤ τ h := by
    have e := hcap h h hs rfl
    rw [min_eq_right hρh] at e
    exact e ▸ min_le_left _ _
  refine ⟨fun e ↦ ?_, hP, ?_, hτh, fun w hw hwk hws ↦ ?_, hρ.monotone.comp hθ.monotone⟩
  · change ρ (orbitDecoder k f h (orbitCode k f e)) = pe e
    rw [hlit e, hread e]
  · change c ≤ ρ (orbitDecoder k f h h)
    refine hρh.trans (hρ.monotone ?_)
    unfold orbitDecoder
    rw [min_self]
    exact le_max_left _ _
  · change min (ρ (orbitDecoder k f h w)) c = _
    rw [orbitDecoder_of_visibilityReplace_lt hw hwk]
    exact hcap w w hws rfl

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-- **Every cell of the attachment has grade at most `m + 1`**: it lies in the context face (on
`m + 1` points) or the donor face (on `n + 1 ≤ m + 1` points). -/
theorem grade_attachment_le (a : Fin (I.attachment g).card) :
    (I.attachment g).toCellScheme.grade a ≤ m + 1 := by
  refine ((I.isWellFormed_attachment g).isWellFormed.grade_le_card a).trans ?_
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  rcases I.scope_attachment g a with h | h
  · exact (card_le_card h).trans (by simp)
  · exact (card_le_card h).trans (by simp; omega)

/-- **At the top grade the orbit code of a lawful state is lawful**: the orbit map is a witness
bounded by `m + 1`, sending only `⊥` to `⊥`, and every cell has grade at most `m + 1`. -/
theorem isLawful_orbitCode_top {W : Fin (I.attachment g).card → Label.{u}}
    (hW : (I.attachment g).rows.IsLawful W) :
    (I.attachment g).rows.IsLawful (orbitCode (m + 1) W) :=
  hW.map_of_bot_iff hW grade_attachment_le (isWitness_orbitMap (m + 1) W)
    fun _ ↦ orbitMap_eq_bot_iff

/-- **Below the top grade the orbit code is not lawful at a positive cell of larger grade**: the
orbit code at `k` is short at `k`, not `⊥` and not the formal top there, so not self-visible at
the grade of the cell. -/
theorem not_isLawful_orbitCode_of_grade_lt {k : ℕ} {W : Fin (I.attachment g).card → Label.{u}}
    {d : Fin (I.attachment g).card} (hd : k < (I.attachment g).toCellScheme.grade d)
    (hW0 : W d ≠ ⊥) : ¬ (I.attachment g).rows.IsLawful (orbitCode k W) := by
  intro hl
  have hv := hl.orderly d
  have hshort := isShort_orbitCode (k := k) (w := W) d
  have hne : orbitCode k W d ≠ ⊥ := fun h ↦ hW0 (orbitCode_eq_bot_iff.mp h)
  have htop := orbitCode_ne_top (k := k) (w := W) d
  generalize orbitCode k W d = y at hv hshort hne htop
  induction y using recBotCoeTop with
  | bot => exact hne rfl
  | top => exact htop rfl
  | coe o =>
    have h1 := isSelfVisible_coe.mp hv
    have h2 := isShort_coe.mp hshort
    have : ((I.attachment g).toCellScheme.grade d : Ordinal.{u}) ≤ (k : Ordinal.{u}) :=
      h1.trans h2
    exact absurd (by exact_mod_cast this) (not_le.mpr hd)

end Seed

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **The test at the top grade `2` of the input**: the orbit code at `2` of the catalogue state of
`TieInstance.gradeGate_fails` (the two-level state of the completion of `sep`) is lawful on the
attachment, as the rendering asks of the coded state. -/
theorem isLawful_orbitCode_gradeGate (I : Seed.{u} ω 1) (hI : I.left = ctx.{u} ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don.{u} ω)) :
    ∃ R₀ ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req.{u} ω))
        (1 + 2),
      I.ReachableCut 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req.{u} ω))
        (I.seedGridBound 𝕣) 2 (topCode.{u} (I.attachment 𝕣).card 4) ∧
      (I.attachment 𝕣).rows.IsLawful (orbitCode 2 R₀) := by
  obtain ⟨R₀, hR₀, -, hcut, -⟩ := gradeGate_fails I hI hdA
  exact ⟨R₀, hR₀, hcut,
    Seed.isLawful_orbitCode_top (Scheme.LadderBaseData.mem_towerCat.mp hR₀).2.1⟩

end TieInstance

end VaughtConjecture

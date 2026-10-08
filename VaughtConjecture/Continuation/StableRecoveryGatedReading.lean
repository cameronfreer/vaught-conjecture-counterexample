/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryMarkedGate
import VaughtConjecture.Extension.Gate

/-!
# Gated reading extensions, and the readers forced in the leaf-and-marked layer

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), Layer 3, 3.3
(the private cap and the decoder of (R4)) and 3.1 (the leaf-and-marked completion); semantic
contract, items 8 and 12.

**Gated reading extensions** (`StageType.IsGatedReadingExtension`, a predicate on one extension).
The reading clause of a cap-reading extension (`StageType.IsCapReadingExtension`) asks every cell
at `(univ, N)` to read the new cells of `D` through the cap.  The gated form asks it only of the
**readers**, a set `S` of cells at `(univ, N)`, and adds a **gate**: a cell `G` at `(univ, N)`
whose row is `⊥` at every other cell there outside `S` (`CellScheme.Rows.ReadsOnly`), reading a
reader (the **ceiling**) at least as itself, and a **display**: a coface of `T⁺↓λ_ξ` on the scheme
labelled other than `⊥` at `G`.  In a lawful labelling not `⊥` at `G`, availability against the cap
reaches a reader (`CellScheme.Rows.IsLawful.exists_mem_le_of_readsOnly`), which decodes; the
bottom-pattern clause of a model applied to the display makes the realized labelling not `⊥` at the
gate (argued here, as for `Realization.IsModel.exists_attachedGate`).  What (R4) would ask of a
construction in this form is the goal (not a named statement, not assumed anywhere): for every
legal `T⁺` at `λ_{ξ+1}`, embedding `f` with face `P`, coface `D` of `P`, `γ < λ_{ξ+1}` and
full-scope graded cap `b`, some scheme, gate and readers form a gated reading extension.

**The readers forced in the leaf-and-marked layer** (`Scheme.markedLayer_gate_false`).  In a
leaf-and-marked layer at the grade `k` with marked closure (`Scheme.MarkedClosed`), let `G` be a
gate reading only a set `T` of cells of `(univ, k)`, with a ceiling `K ∈ T`.  The ceiling has the
entry `e` of `G` (its row reads `G`'s own reading at the ceiling of the field grid).  Let `x` be an
old cell that `e` reads at a value at least the least grid point `k` (outside the natural strip).
Then some cell read by `G` above `⊥`, other than `G`, has as entry the orbit code `b` of `e` capped
at `k` (in the catalogue, agreeing with `e` below `k`, `Scheme.orbitCode_min_gridPoint_zero_mem`),
whose value at `x` is self-visible at `k` (`Label.isSelfVisible_orbitMap`): a mark by marked closure
when the cap of `e` is `⊥`, a leaf otherwise.  So if every member of `T` reads `x` at a value that
is not self-visible at `k` — as the ordinal clause of `StageType.ReadsThroughCap` asks, `ω · c + n`
with `n < N ≤ k` — there is no such gate.  The natural strip (values below `k`) is the only escape.

**In the leaf-and-marked completion**
(`TowerProfile.lt_of_isGatedReadingExtension_markedCompletion`).  On the coatom extension with
apex built from `TowerProfile.markedCompletion`, every ceiling of a gated reading extension for a
cap of grade `4` reads every ordinally labelled new cell of `D` at a natural number below the
least grid point `4`.

**Natural-strip readings keep the labels in one block**
(`CellScheme.Rows.IsLawful.not_natural_strip_of_lt_block`).  If a row reads two cells in the
natural strip, a lawful section cannot label them in two different `ω`-blocks below the label of a
cap at most the label of the reading cell.  So natural-strip readings fail when the labels of the
new cells (on the face at `λ_ξ`) lie in two blocks below the gate's label; when the gate's label is
at most those labels, this argument forces nothing.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme
open Ordinal hiding univ

/-! ### The orbit map keeps self-visibility -/

namespace Label

variable {ι : Type*} [Fintype ι] {w : ι → Label.{u}} {k : ℕ}

/-- **The orbit map keeps self-visibility**: a label other than `⊥`, self-visible at `k`, is sent
to a label self-visible at `k`: off the orbit keys to a grid point, on an orbit key with its finite
part. -/
theorem isSelfVisible_orbitMap {x : Label.{u}} (hx0 : x ≠ ⊥) (hx : IsSelfVisible k x) :
    IsSelfVisible k (orbitMap k w x) := by
  by_cases hO : IsOrbitKey k w x
  · rw [orbitMap_of_isOrbitKey hO]
    induction x using recBotCoeTop with
    | bot => exact absurd rfl hx0
    | top => exact absurd rfl hO.ne_top
    | coe o =>
      -- the block move of an ordinal label keeps its finite part
      change IsSelfVisible k (((ω * blockIndex (gridPoint k (codeBlock k w (o : Label.{u}))) +
        o % ω : Ordinal.{u}) : WithTop Ordinal.{u}) : Label.{u})
      rw [isSelfVisible_coe, Ordinal.mul_add_mod_self,
        Ordinal.mod_eq_of_lt (Ordinal.mod_lt o omega0_ne_zero)]
      exact isSelfVisible_coe.mp hx
  · rw [orbitMap_of_not_isOrbitKey hx0 hO]
    exact isSelfVisible_gridPoint k _

end Label

/-! ### The orbit code of an entry capped at the least grid point -/

namespace Scheme

variable {n k : ℕ} {S : Scheme.{u} n}

/-- **The orbit code of an entry capped at the least grid point** `k` (the splice with `⊥` above
`k`): a catalogue entry, agreeing with the entry capped at `k`, and self-visible at `k` at every
cell where the entry is at least `k`. -/
theorem orbitCode_min_gridPoint_zero_mem {e : Fin S.card → Label.{u}} (he : e ∈ S.catalogue k) :
    orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) fun d ↦ min (e d) (gridPoint k 0)) ∈
        S.catalogue k ∧
      (∀ d, min (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥)
        fun d ↦ min (e d) (gridPoint k 0)) d) (gridPoint k 0) = min (e d) (gridPoint k 0)) ∧
      ∀ x, gridPoint k 0 ≤ e x → IsSelfVisible k (orbitCode k (S.toCellScheme.splice k
        (fun _ ↦ ⊥) fun d ↦ min (e d) (gridPoint k 0)) x) := by
  obtain ⟨hlaw, hup, -⟩ := mem_catalogue.mp he
  set w := S.toCellScheme.splice k (fun _ ↦ ⊥) fun d ↦ min (e d) (gridPoint k 0) with hw
  -- the capped entry is lawful
  have hcap : S.rows.IsLawful fun d ↦ min (e d) (gridPoint k 0) := by
    refine hlaw.min_const fun d hd ↦ ?_
    have hne : e d ≠ ⊥ := ne_bot_of_le_ne_bot (gridPoint_ne_bot k 0) hd
    have hdk : S.toCellScheme.grade d ≤ k := not_lt.mp fun h ↦ hne (hup d h)
    exact (isSelfVisible_gridPoint k 0).mono hdk
  have hwd (d : Fin S.card) : w d = min (e d) (gridPoint k 0) := by
    by_cases hd : S.toCellScheme.grade d ≤ k
    · exact CellScheme.splice_of_le hd
    · rw [hw, CellScheme.splice_of_lt (not_le.mp hd), hup d (not_le.mp hd), min_eq_left bot_le]
  have hww : w = fun d ↦ min (e d) (gridPoint k 0) := funext hwd
  refine ⟨orbitCode_splice_bot_mem_catalogue (hcap.isLawfulBelow (univ, k)), fun d ↦ ?_,
    fun x hx ↦ ?_⟩
  · rw [min_orbitCode_gridPoint_zero, hwd, min_assoc, min_self]
  · rw [orbitCode_apply, hwd x, min_eq_right hx]
    exact isSelfVisible_orbitMap (gridPoint_ne_bot k 0) (isSelfVisible_gridPoint k 0)

/-! ### The gate in the leaf-and-marked layer -/

variable {Mk : Finset (Fin S.card → Label.{u})} {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- Two catalogue entries agreeing capped at the ceiling of the field grid are equal. -/
private theorem eq_of_le_agreementHeight {a b : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (hb : b ∈ S.catalogue k)
    (h : gridPoint k (2 * S.card + 2) ≤ agreementHeight (S.fieldGrid k) a b) : a = b := by
  obtain ⟨-, hag⟩ := agreementHeight_spec (bot_mem_grid k (2 * S.card + 2)) a b
  have hle : agreementHeight (S.fieldGrid k) a b ≤ gridPoint k (2 * S.card + 2) :=
    agreementHeight_le fun x hx ↦ le_gridPoint_of_mem_grid hx
  have hceil {c : Fin S.card → Label.{u}} (hc : c ∈ S.catalogue k) (d : Fin S.card) :
      c d ≤ gridPoint k (2 * S.card + 2) :=
    (le_gridPoint_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue hc d)).trans
      (gridPoint_le_gridPoint.mpr (by omega))
  funext d
  have := hag d
  rwa [le_antisymm hle h, min_eq_left (hceil ha d), min_eq_left (hceil hb d)] at this

/-- **No gate whose readers all read outside the natural strip.**  In the leaf-and-marked layer
at the grade `k` with marked closure, let `G` be a cell at `(univ, k)` whose row is `⊥` at every
other cell there outside `T` (`CellScheme.Rows.ReadsOnly`), with a ceiling `K ∈ T`, and let `x` be
an old cell of grade at most `k` read by `K` at a value at least `k`.  If every member of `T` reads
`x` at a value that is not self-visible at `k`, there is a contradiction: the cell with the orbit
code of the entry of `G` capped at `k` (a mark by marked closure, or a leaf) is read by `G` above
`⊥`, is not `G`, and reads `x` at a value self-visible at `k`. -/
theorem markedLayer_gate_false (hMk : Mk ⊆ S.catalogue k) (hκ : ∀ e, κ e ∈ S.fieldGrid k)
    (hcl : MarkedClosed S k Mk κ) {G K : Fin (S.markedLayer k Mk κ hS).card}
    (hG : (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex G = ((univ : Finset (Fin n)), k))
    {T : Set (Fin (S.markedLayer k Mk κ hS).card)}
    (honly : (S.markedLayer k Mk κ hS).rows.ReadsOnly G T) (hK : K ∈ T)
    (hKG : (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex K =
      (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex G)
    (hceil : (S.markedLayer k Mk κ hS).rows.row G ⟨G, CellScheme.mem_below_gradedIndex _ G⟩ ≤
      (S.markedLayer k Mk κ hS).rows.row G ⟨K, hKG.le⟩)
    {x : Fin S.card} (hxk : S.toCellScheme.grade x ≤ k)
    (hread : ∀ u ∈ T, ∀ hx : Fin.castAdd _ x ∈ (S.markedLayer k Mk κ hS).toCellScheme.below
        ((S.markedLayer k Mk κ hS).toCellScheme.gradedIndex u),
      ¬ IsSelfVisible k ((S.markedLayer k Mk κ hS).rows.row u ⟨_, hx⟩))
    (hout : ∀ hx : Fin.castAdd _ x ∈ (S.markedLayer k Mk κ hS).toCellScheme.below
        ((S.markedLayer k Mk κ hS).toCellScheme.gradedIndex K),
      gridPoint k 0 ≤ (S.markedLayer k Mk κ hS).rows.row K ⟨_, hx⟩) : False := by
  set ε := S.markedEntry k Mk
  set σ := markedSheet (S.catalogue k).card Mk.card
  have hε : ∀ i, ε i ∈ S.catalogue k := markedEntry_mem hMk
  -- the gate and the ceiling are new cells
  obtain ⟨i, rfl⟩ := exists_natAdd_eq_sheetLayer (hS := hS) hG
  obtain ⟨j, rfl⟩ := exists_natAdd_eq_sheetLayer (hS := hS) (hKG.trans hG)
  have hxb {u : Fin ((S.catalogue k).card + Mk.card)} :
      Fin.castAdd _ x ∈ (S.markedLayer k Mk κ hS).toCellScheme.below
        ((S.markedLayer k Mk κ hS).toCellScheme.gradedIndex (Fin.natAdd _ u)) := by
    rw [appendFullCellsScheme_gradedIndex_natAdd]
    exact castAdd_mem_below_sheetLayer hxk
  -- the rows of new cells
  have hrow (u v : Fin ((S.catalogue k).card + Mk.card)) (h) :
      (S.markedLayer k Mk κ hS).rows.row (Fin.natAdd _ u) ⟨Fin.natAdd _ v, h⟩ =
        S.crossHeight k ε σ κ u v := by
    rw [sheetLayer_row_natAdd, sheetRow_natAdd]
  have hrowx (u : Fin ((S.catalogue k).card + Mk.card)) :
      (S.markedLayer k Mk κ hS).rows.row (Fin.natAdd _ u) ⟨_, hxb⟩ = ε u x := by
    rw [sheetLayer_row_natAdd, sheetRow_castAdd]
  -- the ceiling has the entry of the gate
  have hij : ε i = ε j := by
    have h1 := hceil
    rw [hrow i i, hrow i j hKG.le, crossHeight_self] at h1
    refine eq_of_le_agreementHeight (hε i) (hε j) (h1.trans ?_)
    exact min_le_left _ _
  set e := ε i
  have hex : gridPoint k 0 ≤ e x := by
    have := hout hxb
    rwa [hrowx, ← hij] at this
  have hexv : ¬ IsSelfVisible k (e x) := by
    have := hread _ hK hxb
    rwa [hrowx, ← hij] at this
  obtain ⟨hbcat, hbag, hbx⟩ := orbitCode_min_gridPoint_zero_mem (hε i)
  set b := orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) fun d ↦ min (e d) (gridPoint k 0))
  have hagr : gridPoint k 0 ≤ agreementHeight (S.fieldGrid k) e b :=
    le_agreementHeight (gridPoint_mem_grid (Nat.zero_le _)) fun d ↦ (hbag d).symm
  -- a cell with entry `b`, read by the gate above `⊥`
  obtain ⟨z, hzb, hzG⟩ : ∃ z, ε z = b ∧ gridPoint k 0 ≤ S.crossHeight k ε σ κ i z := by
    by_cases hc : σ i = true ∧ κ e = ⊥
    · -- a marked gate of cap `⊥`: the mark of `b`, by marked closure
      have hmk : e ∈ Mk := by
        obtain ⟨m, hm⟩ : ∃ m, Fin.natAdd (S.catalogue k).card m = i := by
          induction i using Fin.addCases with
          | left i' => exact absurd hc.1 (by simp [σ])
          | right m => exact ⟨m, rfl⟩
        -- the entry of the gate, at the marked cell `m`
        change S.markedEntry k Mk i ∈ Mk
        rw [← hm]
        rw [markedEntry_natAdd]
        exact markEntry_mem Mk m
      have hbMk : b ∈ Mk := hcl e hmk b hbcat (gridPoint k 0) (isSelfVisible_gridPoint k 0)
        (isShort_gridPoint k 0) (WithBot.bot_lt_coe _)
        (not_le.mpr (by rw [hc.2]; exact WithBot.bot_lt_coe _)) hbag
      obtain ⟨z, hz, hσz⟩ := exists_mark_eq (k := k) hbMk
      refine ⟨z, hz, ?_⟩
      rw [crossHeight_of_eq (hc.1.trans hσz.symm), show ε z = b from hz]
      exact hagr
    · -- otherwise: the leaf of `b`
      obtain ⟨z, hz, hσz⟩ := exists_leaf_eq (Mk := Mk) hbcat
      refine ⟨z, hz, ?_⟩
      by_cases hs : σ i = σ z
      · rw [crossHeight_of_eq hs, show ε z = b from hz]
        exact hagr
      · rw [crossHeight_of_ne hs, show ε z = b from hz]
        refine le_min hagr ?_
        -- the gate is marked, so its cap is not `⊥`, hence at least the least grid point
        have hmark : σ i = true := by
          have hs' : σ i ≠ false := fun h ↦ hs (h.trans hσz.symm)
          simpa using hs'
        have hne : κ e ≠ ⊥ := fun h ↦ hc ⟨hmark, h⟩
        rcases mem_grid.mp (hκ e) with h | ⟨c, -, hc'⟩
        · exact absurd h hne
        · rw [hc']
          exact gridPoint_le_gridPoint.mpr (Nat.zero_le _)
  -- `z` is not the gate: its value at `x` is self-visible, the gate's is not
  have hzne : Fin.natAdd S.card z ≠ Fin.natAdd S.card i := by
    intro h
    have hzi : z = i := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
    apply hexv
    have := hbx x hex
    rwa [← hzb, hzi] at this
  have hzgi : (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex (Fin.natAdd _ z) =
      (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex (Fin.natAdd _ i) := by
    rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
  -- so `z` is in `T`, and reads `x` at a self-visible value
  have hzT : Fin.natAdd S.card z ∈ T := by
    by_contra hzT
    have h0 := honly _ hzgi hzne hzT
    rw [hrow i z hzgi.le] at h0
    rw [h0] at hzG
    exact absurd hzG (not_le.mpr (WithBot.bot_lt_coe _))
  have := hread _ hzT hxb
  rw [hrowx, hzb] at this
  exact this (hbx x hex)

end Scheme

/-! ### Gated reading extensions -/

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- A **gated reading extension** of `T⁺` along `f` for `D` and the cap `b` of grade `N`: a legal
scheme `E` with the faces of a cap-reading extension, a **gate** `G` at `(univ, N)` whose row is
`⊥` at every other cell there outside the **readers** `S` (`CellScheme.Rows.ReadsOnly`) and reads
some reader (a **ceiling**) at least as itself, readers at `(univ, N)` that read every new cell of
`D` through the cap, and a **display**: a coface of `T⁺↓λ_ξ` on `E` not `⊥` at the gate. -/
structure IsGatedReadingExtension (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (b : Fin Tp.card)
    (E : Scheme.{u} (m + 1)) (G : Fin E.card) (S : Set (Fin E.card)) : Prop where
  /-- The scheme is legal. -/
  isLegal : E.IsLegal
  /-- The first points span a face. -/
  mem_faces_castSuccEmb : univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces
  /-- The face along the first points is the scheme of `T⁺`. -/
  comap_castSuccEmb : E.comap Fin.castSuccEmb = Tp.toScheme
  /-- The root and the new point span a face. -/
  mem_faces_extendByLast : univ.map (extendByLast f) ∈ E.toCellScheme.faces
  /-- The face along the root and the new point is the scheme of `D`. -/
  comap_extendByLast : E.comap (extendByLast f) = D.toScheme
  /-- The gate is at `(univ, N)`. -/
  gradedIndex_gate : E.toCellScheme.gradedIndex G =
    ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b)
  /-- The gate reads only the readers at its graded index. -/
  readsOnly : E.rows.ReadsOnly G S
  /-- The gate reads a reader at least as itself. -/
  exists_ceiling : ∃ K ∈ S, ∃ hKG : E.toCellScheme.gradedIndex K = E.toCellScheme.gradedIndex G,
    E.rows.row G ⟨G, CellScheme.mem_below_gradedIndex _ G⟩ ≤ E.rows.row G ⟨K, hKG.le⟩
  /-- The readers are at `(univ, N)` and read every new cell of `D` through the cap. -/
  readers : ∀ u ∈ S, E.toCellScheme.gradedIndex u = E.toCellScheme.gradedIndex G ∧
    ∃ b' : Fin (E.comap Fin.castSuccEmb).card, (b' : ℕ) = b ∧
      ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
        Fin.last k ∈ D.toCellScheme.scope j →
          Tp.ReadsThroughCap E b' u (E.cellMap (extendByLast f) i) (D.label j)
  /-- A coface of `T⁺↓λ_ξ` on `E`, not `⊥` at the gate. -/
  display : ∃ q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces, q.toScheme = E ∧
    ∀ i : Fin q.card, (i : ℕ) = G → q.label i ≠ ⊥

/-- **Recovery in a gated reading extension**: for a graded cap `b`, every stage type `Q'` at
`λ_{ξ+1}` on `E` with face `T⁺` and not `⊥` at the gate has, along `f` followed by the new point,
a face on the scheme of `D` that agrees with `D` off the formal top and lies above `γ` at the
formal top.  Availability against the cap reaches a reader
(`CellScheme.Rows.IsLawful.exists_mem_le_of_readsOnly`), which decodes the new cells
(`CellScheme.Rows.IsLawful.label_eq_of_reading` and its companions), as in
`StageType.IsStableRecoveryScheme.of_readsThroughCap`. -/
theorem IsGatedReadingExtension.recover {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {P : StageType.{u} (blockStage (ξ + 1)) k}
    (hP : restrictFace f Tp = some P) {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)}
    (hD : D ∈ P.cofaces) {γ : Ordinal.{u}} {b : Fin Tp.card} (hcap : IsGradedCap ξ Tp D γ b)
    {E : Scheme.{u} (m + 1)} {G : Fin E.card} {S : Set (Fin E.card)}
    (h : IsGatedReadingExtension Tp f D b E G S) (Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (hQ'E : Q'.toScheme = E) (hQ'f : restrictFace Fin.castSuccEmb Q' = some Tp)
    (hG : ∀ i : Fin Q'.card, (i : ℕ) = G → Q'.label i ≠ ⊥) :
    ∃ Q, restrictFace (extendByLast f) Q' = some Q ∧ Q.toScheme = D.toScheme ∧
      ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
        (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
          (D.label j = ⊤ → (γ : Label.{u}) < Q.label i) := by
  subst hQ'E
  obtain ⟨-, -, hcT', hf, hED, hGidx, honly, ⟨K, hKS, hKG, hceil⟩, hreaders, -⟩ := h
  obtain ⟨hb, hkN, hγ, -⟩ := hcap
  refine ⟨Q'.comap (extendByLast f) hf, restrictFace_of_mem _ _ hf, hED, fun i j hij ↦ ?_⟩
  -- the labels of `Q'` at the cells of `T⁺`
  obtain ⟨_, hcT⟩ := (restrictFace_eq_some_iff _ _).mp hQ'f
  have hlab {a : Fin (Q'.toScheme.comap Fin.castSuccEmb).card} {a₀ : Fin Tp.card}
      (h : (a : ℕ) = a₀) : Q'.label (Q'.cellMap Fin.castSuccEmb a) = Tp.label a₀ :=
    label_congr hcT h
  by_cases hj : Fin.last k ∈ D.toCellScheme.scope j
  swap
  · -- an old cell: the face along `f` followed by the new point and `D` have the face `P`
    have hQP : restrictFace Fin.castSuccEmb (Q'.comap (extendByLast f) hf) = some P := by
      rw [restrictFace_trans Q' _ _ (restrictFace_of_mem Q' _ hf),
        castSuccEmb_trans_extendByLast, ← restrictFace_trans Q' _ _ hQ'f, hP]
    have hvis : j ∈ D.visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro x hx
      induction x using Fin.lastCases with
      | last => exact absurd hx hj
      | cast x => exact ⟨x, rfl⟩
    have hl := label_eq_of_mem_visibleCells hED hQP hD.2 hij hvis
    refine ⟨fun _ ↦ hl, fun h ↦ ?_⟩
    rw [hl, h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  -- the cap, as a cell of the face along the first points
  have hcard : (Q'.toScheme.comap Fin.castSuccEmb).card = Tp.card := congrArg Scheme.card hcT'
  set c : Fin (Q'.toScheme.comap Fin.castSuccEmb).card := Fin.cast hcard.symm b
  have hgc : Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) = Tp.toCellScheme.grade b :=
    Scheme.grade_congr hcT' rfl
  have hpb : ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤
      Q'.label (Q'.cellMap Fin.castSuccEmb c) := hb.trans_eq (hlab rfl).symm
  -- availability against the cap reaches a reader
  have hGne : Q'.label G ≠ ⊥ := hG G rfl
  have hCG : Q'.toCellScheme.scope (Q'.cellMap Fin.castSuccEmb c) ⊆ Q'.toCellScheme.scope G := by
    rw [show Q'.toCellScheme.scope G = univ from congrArg Prod.fst hGidx]
    exact subset_univ _
  have hgr : Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) = Q'.toCellScheme.grade G := by
    rw [hgc, show Q'.toCellScheme.grade G = _ from congrArg Prod.snd hGidx]
  obtain ⟨u, hu, hug, hbu⟩ :=
    Q'.isLawful.exists_mem_le_of_readsOnly honly hKS hKG hceil hGne hCG hgr
  obtain ⟨-, b', hb'b, hread⟩ := hreaders u hu
  obtain rfl : b' = c := Fin.ext hb'b
  have huidx : Q'.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 1))), Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c)) := by
    rw [hug, hGidx, hgc]
  have hwf := Q'.isWellFormed.comap (extendByLast f) hf
  have heb : Q'.toCellScheme.grade (Q'.cellMap (extendByLast f) i) ≤
      Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) := by
    have h1 := (hwf.isWellFormed.grade_le_card i).trans
      ((card_le_univ _).trans_eq (Fintype.card_fin (k + 1)))
    -- the grade of a cell of the face is the grade of its image
    change (Q'.toScheme.comap (extendByLast f)).toCellScheme.grade i ≤ _
    rw [hgc]
    omega
  have he' : Q'.cellMap (extendByLast f) i ∈
      Q'.toCellScheme.below (Q'.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, huidx]
    exact ⟨subset_univ _, heb⟩
  have hc : Q'.cellMap Fin.castSuccEmb c ∈
      Q'.toCellScheme.below (Q'.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, huidx]
    exact ⟨subset_univ _, le_rfl⟩
  have hgu : Q'.toCellScheme.grade u = Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) :=
    congrArg Prod.snd huidx
  have hpc : ((blockStage ξ + Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) :
      Ordinal.{u}) : Label.{u}) ≤ Q'.label (Q'.cellMap Fin.castSuccEmb c) := by
    rw [hgc]
    exact hpb
  have hpu : Q'.label u ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (hpc.trans hbu)
  obtain ⟨hbot, htop, hord⟩ := hread i j hij hj he' hc
  -- the label of the face at `i` is the label of `Q'` at the new cell
  change (D.label j ≠ ⊤ → Q'.label (Q'.cellMap (extendByLast f) i) = D.label j) ∧
    (D.label j = ⊤ → (γ : Label.{u}) < Q'.label (Q'.cellMap (extendByLast f) i))
  rcases atStage_iff.mp (D.atStage j) with h | ⟨o, ho, h⟩ | h
  · -- `D` is `⊥` at `j`: the row reads the new cell as `⊥`
    refine ⟨fun _ ↦ ?_, fun h' ↦ absurd (h.symm.trans h') bot_ne_top⟩
    rw [h]
    exact CellScheme.Rows.IsLawful.label_eq_bot_of_reading Q'.isLawful he' (hbot h) hpu
  · -- `D` is an ordinal `μ + n` at `j`: the decoder through a reference cell
    obtain ⟨μ, n, hμ, rfl, hμξ⟩ : ∃ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ ∧
        o = μ + n ∧ (μ < blockStage ξ ∨ μ = blockStage ξ) := by
      rcases lt_or_ge o (blockStage ξ) with hlt | hge
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
          (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
        exact ⟨ω * (o / ω), n, Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          hn, Or.inl ((Ordinal.mul_div_le o ω).trans_lt hlt)⟩
      · rw [blockStage_add_one] at ho
        obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hge ho
        exact ⟨blockStage ξ, n, isSuccPrelimit_blockStage ξ, hn, Or.inr rfl⟩
    obtain ⟨hnN, a, a₀, i', c', haa₀, ha₀, hiN, ha, hra, hre⟩ := hord μ n hμ h.symm
    -- every `μ + x` with `x` below the grade of the cap lies below the cap
    have hlt (x : ℕ) (hx : x < Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c)) :
        ((μ + x : Ordinal.{u}) : Label.{u}) < Q'.label (Q'.cellMap Fin.castSuccEmb c) := by
      refine lt_of_lt_of_le ?_ hpc
      have : μ + x < blockStage ξ + Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) := by
        rcases hμξ with hμξ | rfl
        · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt hμξ x).trans_le
            le_self_add
        · exact add_lt_add_right (Nat.cast_lt.mpr hx) _
      exact_mod_cast this
    refine ⟨fun _ ↦ ?_, fun h' ↦ absurd (h.trans h') (WithBot.coe_lt_coe.mpr
      (WithTop.coe_lt_top _)).ne⟩
    rw [← h]
    exact CellScheme.Rows.IsLawful.label_eq_of_reading Q'.isLawful ha hc he' hμ
      (ha.2.trans hgu.le) hiN hnN.le heb hra hre ((hlab haa₀).trans ha₀) hbu (hlt i' hiN)
      (hlt n hnN)
  · -- `D` is the formal top at `j`: the row reads the new cell as the cap
    refine ⟨fun h' ↦ absurd h h', fun _ ↦ ?_⟩
    have hγ' : (γ : Label.{u}) <
        ((blockStage ξ + Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb c) : Ordinal.{u}) :
          Label.{u}) := by
      rw [hgc]
      exact_mod_cast hγ
    exact hγ'.trans_le (hpc.trans (CellScheme.Rows.IsLawful.le_label_of_reading Q'.isLawful hc
      he' heb (htop h) hbu))

end StageType

/-! ### Natural-strip readings keep the labels in one block -/

namespace CellScheme.Rows.IsLawful

open Ordinal

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows}

/-- **Natural-strip readings keep the labels in one block.**  In a lawful section `p`, let the
row of a cell `s` read two cells `a` and `e` in the natural strip, at naturals `i` and `o`, with
the grades of `a` and `e` at most that of a cell `b` with `p b ≤ p s`, `i < grade b` and
`o ≤ grade b`.  If `p a = μ + i` and `p e = μ' + o'` lie in two different `ω`-blocks (`μ < μ'`,
both zero or a limit) with `p e` strictly below `p b`, the section is impossible: the decoder
(`CellScheme.Rows.IsLawful.label_eq_of_reading` with block `0`) puts `p e` in the block of `μ`.
The hypothesis `p e < p b` (both labels below the cap's label) is needed: when the label of `b`
is at most the labels read, nothing is forced. -/
theorem not_natural_strip_of_lt_block {p : ι → Label.{u}} (h : R.IsLawful p) {s a b e : ι}
    (ha : a ∈ D.below (D.gradedIndex s)) (hb : b ∈ D.below (D.gradedIndex s))
    (he : e ∈ D.below (D.gradedIndex s)) {μ μ' : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hμ' : Order.IsSuccPrelimit μ') (hμμ' : μ < μ') {i o o' : ℕ} (hab : D.grade a ≤ D.grade b)
    (hi : i < D.grade b) (ho : o ≤ D.grade b) (heb : D.grade e ≤ D.grade b)
    (hra : R.row s ⟨a, ha⟩ = ((i : Ordinal.{u}) : Label.{u}))
    (hre : R.row s ⟨e, he⟩ = ((o : Ordinal.{u}) : Label.{u}))
    (hpa : p a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hpe : p e = ((μ' + o' : Ordinal.{u}) : Label.{u})) (hbs : p b ≤ p s) (heb' : p e < p b) :
    False := by
  have hlt (n : ℕ) : ((μ + n : Ordinal.{u}) : Label.{u}) < p b := by
    refine lt_of_lt_of_le ?_ (hpe ▸ heb').le
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      ((hμ'.add_natCast_lt hμμ' n).trans_le (le_self_add)))
  have key := h.label_eq_of_reading ha hb he hμ (c := 0) hab hi ho heb
    (by rw [mul_zero, zero_add]; exact hra) (by rw [mul_zero, zero_add]; exact hre) hpa hbs
    (hlt i) (hlt o)
  rw [hpe] at key
  have key' : μ' + o' = μ + o := WithTop.coe_injective (WithBot.coe_injective key)
  exact lt_irrefl _ ((hμ'.add_natCast_lt hμμ' o).trans_le (le_self_add.trans_eq key'))

end CellScheme.Rows.IsLawful

/-! ### The leaf-and-marked completion: only the natural strip -/

namespace TowerProfile

variable {ξ : Ordinal.{u}} {I : Seed.{u} (blockStage (ξ + 1)) 3} (D : MarkedSpec I)

-- The scheme of the coatom extension with apex built from the leaf-and-marked completion (the
-- check of unbound identifiers is off: `I`, `D` and `ξ` are the section variables).
set_option quotPrecheck false in
local notation "𝔼" =>
  ((markedCompletion I D).completion (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit).toScheme

/-- **In the leaf-and-marked completion, a gated ceiling reads in the natural strip.**  Let the
scheme `𝔼` of the coatom extension with apex built from the leaf-and-marked completion of a seed
(`CompletionBelowFullGrade.completion` of `TowerProfile.markedCompletion I D`) carry a gated
reading extension of the first coatom type along `f.trans Fin.castSuccEmb` for `Dn` and a cap of
grade `4`, with gate `G` and readers `S`.  Then every ceiling `K` of `G` in `S` reads every new
cell of `Dn` with a label `μ + n` (`μ` a limit or zero) at a value below the least grid point at
`4`.  Otherwise `Scheme.markedLayer_gate_false` applies on the marked top: the readers read that
cell at values `ω · c + n` with `n < 4`, not self-visible at `4`. -/
theorem lt_of_isGatedReadingExtension_markedCompletion {k : ℕ} (f : Fin k ↪ Fin 3)
    (Dn : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (b : Fin I.left.card)
    (hb4 : I.left.toCellScheme.grade b = 4) {G : Fin (𝔼).card} {S : Set (Fin (𝔼).card)}
    (h : StageType.IsGatedReadingExtension I.left (f.trans Fin.castSuccEmb) Dn b 𝔼 G S)
    {K : Fin (𝔼).card} (hKS : K ∈ S)
    (hKG : (𝔼).toCellScheme.gradedIndex K = (𝔼).toCellScheme.gradedIndex G)
    (hceil : (𝔼).rows.row G ⟨G, CellScheme.mem_below_gradedIndex _ G⟩ ≤
      (𝔼).rows.row G ⟨K, hKG.le⟩)
    {j : Fin Dn.card} (hj : Fin.last k ∈ Dn.toCellScheme.scope j) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {n : ℕ} (hD : Dn.label j = ((μ + n : Ordinal.{u}) : Label.{u}))
    (i : Fin ((𝔼).comap (extendByLast (f.trans Fin.castSuccEmb))).card) (hij : (i : ℕ) = j)
    (he : (𝔼).cellMap (extendByLast (f.trans Fin.castSuccEmb)) i ∈
      (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex K)) :
    (𝔼).rows.row K ⟨_, he⟩ < gridPoint 4 0 := by
  obtain ⟨-, -, hT, -, -, hGidx, honly, -, hreaders, -⟩ := h
  by_contra hge
  rw [not_lt] at hge
  have hlegal := (markedCompletion I D).isLegalBelowFullGrade
  -- the cells of `𝔼` at `(univ, 4)` are cells of the marked top
  have hold (z : Fin (𝔼).card) (hz : (𝔼).toCellScheme.gradedIndex z =
      ((univ : Finset (Fin 5)), 4)) : ∃ z₀ : Fin (markedTop I D).card, Fin.castSucc z₀ = z := by
    have hne : z ≠ Fin.last _ := by
      intro hl
      have h5 : (𝔼).toCellScheme.gradedIndex (Fin.last _) = ((univ : Finset (Fin 5)), 5) :=
        Scheme.appendFullCellScheme_gradedIndex_last _ _
      rw [← hl, hz] at h5
      exact absurd (congrArg Prod.snd h5) (by decide)
    exact ⟨z.castPred hne, Fin.castSucc_castPred z hne⟩
  have hgi (z₀ : Fin (markedTop I D).card) : (𝔼).toCellScheme.gradedIndex (Fin.castSucc z₀) =
      (markedTop I D).toCellScheme.gradedIndex z₀ :=
    Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z₀
  have hrowE (s t : Fin (markedTop I D).card)
      (ht : t ∈ (markedTop I D).toCellScheme.below ((markedTop I D).toCellScheme.gradedIndex s))
      (ht' : Fin.castSucc t ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castSucc s))) :
      (𝔼).rows.row (Fin.castSucc s) ⟨_, ht'⟩ = (markedTop I D).rows.row s ⟨t, ht⟩ :=
    Scheme.appendFullCell_row_castSucc_castSucc (S := markedTop I D) (j := 5)
      (h := hlegal.not_le) s t ht ht'
  have hG4 : (𝔼).toCellScheme.gradedIndex G = ((univ : Finset (Fin 5)), 4) := by
    rw [hGidx, hb4]
  obtain ⟨G₀, rfl⟩ := hold G hG4
  obtain ⟨K₀, rfl⟩ := hold _ (hKG.trans hG4)
  have hG₀ : (markedTop I D).toCellScheme.gradedIndex G₀ = ((univ : Finset (Fin 5)), 4) :=
    (hgi G₀).symm.trans hG4
  have hK₀G₀ : (markedTop I D).toCellScheme.gradedIndex K₀ =
      (markedTop I D).toCellScheme.gradedIndex G₀ := by
    rw [← hgi, ← hgi]
    exact hKG
  -- the new cell is an old cell of the amalgam
  have hk3 : k ≤ 3 := by simpa using Fintype.card_le_of_embedding f
  have hscope : (𝔼).toCellScheme.scope
      ((𝔼).cellMap (extendByLast (f.trans Fin.castSuccEmb)) i) ≠ univ := by
    intro hu'
    have hsub := (𝔼).cellMap_mem (extendByLast (f.trans Fin.castSuccEmb)) i
    rw [Scheme.visibleCells, Finset.mem_filter, hu'] at hsub
    have hc := card_le_card hsub.2
    rw [card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at hc
    omega
  obtain ⟨z, hz⟩ : ∃ z : Fin (markedTop I D).card,
      Fin.castSucc z = (𝔼).cellMap (extendByLast (f.trans Fin.castSuccEmb)) i := by
    have hne : (𝔼).cellMap (extendByLast (f.trans Fin.castSuccEmb)) i ≠ Fin.last _ := by
      intro hl
      apply hscope
      rw [hl]
      exact Scheme.appendFullCellScheme_scope_last _ _
    exact ⟨_, Fin.castSucc_castPred _ hne⟩
  have hzs : (markedTop I D).toCellScheme.scope z ≠ univ := by
    rw [← Scheme.appendFullCellScheme_scope_castSucc (markedTop I D) 5 z, hz]
    exact hscope
  obtain ⟨d, rfl⟩ := mem_range_markedEmbed D z hzs
  have hxk : (scheme I).toCellScheme.grade (embed3 I d) ≤ 4 := by
    have h1 := (isLowerEmbedding_embed3 (I := I)).grade_eq d
    have h2 := I.grade_lt d
    omega
  -- membership below a cell at `(univ, 4)`
  have hbelow (s : Fin (markedTop I D).card)
      (hs : (markedTop I D).toCellScheme.gradedIndex s = ((univ : Finset (Fin 5)), 4)) :
      markedEmbed I D d ∈
        (markedTop I D).toCellScheme.below ((markedTop I D).toCellScheme.gradedIndex s) := by
    rw [hs]
    exact Scheme.castAdd_mem_below_sheetLayer (hS := not_univ_four_le) hxk
  have hbelowE (s : Fin (markedTop I D).card)
      (hs : (markedTop I D).toCellScheme.gradedIndex s = ((univ : Finset (Fin 5)), 4)) :
      Fin.castSucc (markedEmbed I D d) ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castSucc s)) := by
    exact (hgi _).trans_le ((hbelow s hs).trans_eq (hgi s).symm)
  refine Scheme.markedLayer_gate_false (S := scheme I) (k := 4) (hS := not_univ_four_le)
    D.marks_subset D.cap_mem D.closed
    (G := G₀) (K := K₀) hG₀ (T := {u₀ | Fin.castSucc u₀ ∈ S}) ?_ hKS hK₀G₀ ?_ hxk ?_ ?_
  · -- the gate reads only the readers
    intro t₀ ht₀ htne htT
    have hE0 := honly (Fin.castSucc t₀) ((hgi t₀).trans (ht₀.trans (hgi G₀).symm))
      (fun h' ↦ htne (Fin.castSucc_injective _ h')) htT
    exact (hrowE G₀ t₀ ht₀.le _).symm.trans hE0
  · -- the ceiling, on the marked top
    rw [← hrowE G₀ G₀ (CellScheme.mem_below_gradedIndex _ G₀)
      (CellScheme.mem_below_gradedIndex _ _), ← hrowE G₀ K₀ hK₀G₀.le]
    exact hceil
  · -- the readers read the new cell at a value that is not self-visible at `4`
    intro u₀ hu₀ hx
    have hu₀4 : (markedTop I D).toCellScheme.gradedIndex u₀ = ((univ : Finset (Fin 5)), 4) := by
      exact (hgi u₀).symm.trans ((hreaders _ hu₀).1.trans hG4)
    obtain ⟨-, b', hb'b, hread⟩ := hreaders _ hu₀
    have hgb : (𝔼).toCellScheme.grade ((𝔼).cellMap Fin.castSuccEmb b') = 4 :=
      (Scheme.grade_congr hT hb'b).trans hb4
    have hb : (𝔼).cellMap Fin.castSuccEmb b' ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castSucc u₀)) := by
      -- membership below is the order on graded indices
      change _ ≤ (𝔼).toCellScheme.gradedIndex (Fin.castSucc u₀)
      rw [(hgi u₀).trans hu₀4]
      exact ⟨subset_univ _, hgb.le⟩
    obtain ⟨-, -, hord⟩ := hread i j hij hj (hz ▸ hbelowE u₀ hu₀4) hb
    obtain ⟨hnN, _, _, _, c, _, _, _, _, _, hre⟩ := hord μ n hμ hD
    have hc : Order.IsSuccPrelimit (ω * c) :=
      Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)
    have hval : (markedTop I D).rows.row u₀ ⟨_, hx⟩ =
        ((ω * c + n : Ordinal.{u}) : Label.{u}) := by
      rw [← hrowE u₀ _ hx (hbelowE u₀ hu₀4)]
      exact ((𝔼).rows.row_congr rfl hz).trans hre
    rw [hval]
    exact not_isSelfVisible_coe_add_natCast hc (by rw [hgb] at hnN; exact hnN)
  · -- the ceiling reads the new cell at least at `4`
    intro hx
    have hK₀4 : (markedTop I D).toCellScheme.gradedIndex K₀ = ((univ : Finset (Fin 5)), 4) :=
      hK₀G₀.trans hG₀
    rw [← hrowE K₀ _ hx (hbelowE K₀ hK₀4)]
    exact hge.trans_eq ((𝔼).rows.row_congr rfl hz.symm)

end TowerProfile

end VaughtConjecture

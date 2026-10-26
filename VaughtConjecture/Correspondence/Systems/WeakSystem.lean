/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Base
import VaughtConjecture.MainTheorem.Spectrum

/-!
# Weak systems: [AFK26, Definitions 2.17, 2.20, 2.21]

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For an
invariance diagram `D` and an invariant system `S` on an arbitrary geometry signature `σ`:

* `WeakSystem D S` [AFK26, Definition 2.17]: classes `K β M` of structures on each carrier `M` (in
  one universe `v`), indexed by the countable ordinals `β` (`SystemLevel`), with the fields
  `compatibleWith` (the printed standing hypothesis that `D` and `S` are compatible),
  `nonempty`, `isoClosed`, `isCompatible`, `fixed`, `dense`, `projection_mem`;
* the base and the lifts, `WeakSystem.IsLiftAt` and `WeakSystem.IsInBase` [AFK26, Definition 2.17];
* maximality, `WeakSystem.IsMaximalAt` and `WeakSystem.IsMaximal`, and few maximal models,
  `WeakSystem.HasFewMaximal` [AFK26, Definition 2.20], with the coding passage to the canonical
  carriers `Fin (n + 1)` and `ℕ`, `WeakSystem.HasFewMaximalOnCanonicalCarriers`;
* eventual determination, `WeakSystem.IsEventuallyDeterminedTuple` and
  `WeakSystem.IsEventuallyDetermined` [AFK26, Definition 2.21], with the printed **strict**
  inequality `α* > α`;
* the isomorphism classes of the base on the canonical carriers `Fin (n + 1)` and `ℕ`,
  `WeakSystem.BaseClasses` (from `WeakSystem.baseIsoSetoid`), the type counted by the general form
  of [AFK26, Theorem 2.25 (a)];
* the base axiomatized by a sentence on the codes on `ℕ`, `WeakSystem.IsBaseSentence`, and on all
  countable nonempty carriers, `WeakSystem.IsBaseSentenceOnCarriers`;
* the extra hypothesis of the statements that count only models on `ℕ`,
  `WeakSystem.CountableMembersInfinite` (never a field).

**Countability and nonemptiness.**  [AFK26, Definition 2.17] puts countability into `K_β`
("countable structures") and [AFK26, §1] makes every domain nonempty.  Here nonemptiness is the
field `nonempty`; countability is a premise: every field that asserts membership
(`isoClosed`, `projection_mem`) carries `[Countable _]` on the carrier of the asserted member, and
so does every condition and theorem that quantifies over carriers.  A printed system, with
countability inside its classes, is therefore an instance; so is `K[L]`, whose classes do not
contain countability.

**Indices.**  `K` is indexed by `SystemLevel = {β : Ordinal.{0} // β < ω₁}`, as `InvariantSystem`.
Order on levels is the order of the subtype.

**The printed inequalities.**  Projection closure is for `α < β`, as printed (`α = β` follows from
`fixed`).  Maximality at `β` quantifies over `β* > β` and allows an unchanged higher lift.
Eventual determination quantifies over `α* > α_ā`, strictly, as printed.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-- **A weak system** [AFK26, Definition 2.17] for an invariance diagram `D` and an invariant system
`S`: for every countable `β` and carrier `M` (in the universe `v`), a set `K β M` of structures on
`M`, one field for each printed requirement:

* `compatibleWith`: `D` and `S` are compatible ([AFK26, Definition 2.8]; the printed standing
  hypothesis "`τ` compatible with `ID`");
* `nonempty`: members have nonempty carriers ([AFK26, §1]);
* `isoClosed`: `K_β` is closed under isomorphism, on countable carriers;
* `isCompatible`: members are compatible with `D` ([AFK26, Definition 2.5]);
* `fixed`: members of `K_β` have rank at most `β` (`τ_β(G) = G`);
* `dense`: members of `K_β` are `α`-dense for every `α < β` ([AFK26, Definition 2.10 (c)]);
* `projection_mem`: on a countable carrier, `τ_α(G) ∈ K_α` for `G ∈ K_β` and `α < β`.

Countability is a premise of the membership assertions, not a clause of `K`.  Correspondence with
the printed definitions. -/
structure WeakSystem (D : InvarianceDiagram σ) (S : InvariantSystem.{0} σ) where
  /-- The classes `K_β`, on each carrier. -/
  K : SystemLevel → ∀ M : Type v, Set (L.Structure M)
  /-- The diagram and the invariant system are compatible ([AFK26, Definition 2.8]). -/
  compatibleWith : D.IsCompatibleWith S
  /-- Members have nonempty carriers ([AFK26, §1]). -/
  nonempty ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ : G ∈ K β M → Nonempty M
  /-- `K_β` is closed under isomorphism, on countable carriers. -/
  isoClosed ⦃β : SystemLevel⦄ ⦃M N : Type v⦄ [Countable N] ⦃G : L.Structure M⦄
    ⦃H : L.Structure N⦄ : G ∈ K β M → Nonempty (@Language.Equiv L M N G H) → H ∈ K β N
  /-- Members are compatible with `D`. -/
  isCompatible ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ :
    G ∈ K β M → @InvarianceDiagram.IsCompatible L σ D M G
  /-- Members of `K_β` have rank at most `β`. -/
  fixed ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ : G ∈ K β M → S.IsFixedAt β G
  /-- Members of `K_β` are `α`-dense for every `α < β`. -/
  dense ⦃α β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ :
    α < β → G ∈ K β M → D.IsDenseAt S α G
  /-- On a countable carrier, `K_β` projects into `K_α` for `α < β`. -/
  projection_mem ⦃α β : SystemLevel⦄ ⦃M : Type v⦄ [Countable M] ⦃G : L.Structure M⦄ :
    α < β → G ∈ K β M → S.projection α G ∈ K α M

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', v} D S)
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-! ### The base and lifts -/

/-- **`G` is a lift of `B` at level `β`** [AFK26, Definitions 2.2 and 2.17]: `G ∈ K_β`, on the same
carrier, and `G↾L_c = B`.  Correspondence with the printed definitions. -/
def IsLiftAt (β : SystemLevel) {M : Type v} (G : L.Structure M) (B : Lc.Structure M) : Prop :=
  G ∈ W.K β M ∧ E.reduct G = B

/-- **The base** `K_{-∞} = {G↾L_c : G ∈ K}` [AFK26, Definition 2.17]: `B` has a lift in some
`K_β`, on the same carrier.  Correspondence with the printed definitions. -/
def IsInBase {M : Type v} (B : Lc.Structure M) : Prop :=
  ∃ (β : SystemLevel) (G : L.Structure M), W.IsLiftAt E β G B

/-! ### Maximality -/

/-- **Maximal at level `β`** [AFK26, Definition 2.20]: `G ∈ K_β`, and whenever `β < β*`,
`G* ∈ K_{β*}` (on the same carrier) and `τ_β(G*) = G`, then `G = G*`.  The printed definition
**allows an unchanged higher lift**: `G` may itself be a member of `K_{β*}` for `β* > β` (then
`τ_β(G) = G` and the conclusion `G = G` holds); maximality forbids only a different lift.
Correspondence with the printed definitions. -/
def IsMaximalAt (β : SystemLevel) {M : Type v} (G : L.Structure M) : Prop :=
  G ∈ W.K β M ∧ ∀ β' : SystemLevel, β < β' → ∀ G' ∈ W.K β' M, S.projection β G' = G → G = G'

/-- **Maximal** [AFK26, Definition 2.20]: maximal at some level.  Correspondence with the printed
definitions. -/
def IsMaximal {M : Type v} (G : L.Structure M) : Prop :=
  ∃ β : SystemLevel, W.IsMaximalAt β G

/-- **Few maximal models** [AFK26, Definition 2.20]: for every countable `β`, the structures maximal
at `β` are countably many up to isomorphism: there are countably many countable carriers `C i`
(in the universe `v`, finite or infinite) with structures maximal at `β`, and every structure
maximal at `β` on a countable carrier is isomorphic to one of them.  Finite carriers are allowed,
as printed; representatives on `ℕ` alone would strengthen the condition.  The passage to the
canonical carriers `Fin (n + 1)` and `ℕ` is `HasFewMaximalOnCanonicalCarriers` and the stated
target `FewMaximalCodingTarget`.  Correspondence with the printed definitions. -/
def HasFewMaximal : Prop :=
  ∀ β : SystemLevel, ∃ (ι : Type) (_ : Countable ι) (C : ι → Type v)
    (_ : ∀ i, Countable (C i)) (H : ∀ i, L.Structure (C i)),
    (∀ i, W.IsMaximalAt β (H i)) ∧
    ∀ (M : Type v) [Countable M] (G : L.Structure M), W.IsMaximalAt β G →
      ∃ i, Nonempty (@Language.Equiv L M (C i) G (H i))

/-- **Few maximal models on the canonical carriers** (the coding passage for
[AFK26, Definition 2.20], for carriers in universe `0`): for every countable `β`, the structures
maximal at `β` on each **positive finite** carrier `Fin (n + 1)` and on `ℕ` are countably many up to
isomorphism (`IsCountableUpToIso`).  Every countable nonempty carrier is in bijection with one of
these.  Correspondence with the printed definitions. -/
def HasFewMaximalOnCanonicalCarriers (W : WeakSystem.{w, w', 0} D S) : Prop :=
  ∀ β : SystemLevel,
    (∀ n : ℕ, IsCountableUpToIso fun G : L.Structure (Fin (n + 1)) ↦ W.IsMaximalAt β G) ∧
      IsCountableUpToIso fun G : L.Structure ℕ ↦ W.IsMaximalAt β G

/-! ### Eventual determination -/

/-- **A tuple eventually determined** in an `L_c`-structure `B` [AFK26, Definition 2.21]: there
are a countable `α` and an invariant `Q` such that (1) some lift of `B` in `K_α` has `Q(a)`, and
(2) every lift of `B` in `K_{α*}` with `α* > α` — **strictly**, as printed — has `Q(a)`.
Correspondence with the printed definitions. -/
def IsEventuallyDeterminedTuple {M : Type v} (B : Lc.Structure M) {n : ℕ} (a : Fin n → M) :
    Prop :=
  ∃ (α : SystemLevel) (Q : σ.Invariant n),
    (∃ G : L.Structure M, W.IsLiftAt E α G B ∧ RelMap (L := L) (self := G) Q.1 a) ∧
    ∀ α' : SystemLevel, α < α' → ∀ G : L.Structure M, W.IsLiftAt E α' G B →
      RelMap (L := L) (self := G) Q.1 a

/-- **An eventually determined structure** [AFK26, Definition 2.21]: every closed tuple of `B` is
eventually determined.  Correspondence with the printed definitions. -/
def IsEventuallyDetermined {M : Type v} (B : Lc.Structure M) : Prop :=
  ∀ ⦃n : ℕ⦄ (a : Fin n → M), E.IsClosedTuple B a → W.IsEventuallyDeterminedTuple E B a

/-! ### The isomorphism classes of the base on the canonical carriers -/

/-- **Isomorphism of members of the base on one carrier `X`**: `L_c`-isomorphism of the structures.
Correspondence with the printed definitions. -/
def baseIsoSetoid (X : Type v) : Setoid {B : Lc.Structure X // W.IsInBase E B} where
  r B B' := Nonempty (@Language.Equiv Lc X X B.1 B'.1)
  iseqv := ⟨fun B ↦ ⟨@Language.Equiv.refl Lc X B.1⟩,
    fun {B B'} ⟨e⟩ ↦ ⟨@Language.Equiv.symm Lc X X B.1 B'.1 e⟩,
    fun {B B' B''} ⟨e⟩ ⟨f⟩ ↦ ⟨@Language.Equiv.comp Lc X X B.1 B'.1 X B''.1 f e⟩⟩

/-- **The isomorphism classes of the base on the canonical carriers** ([AFK26, Theorem 2.25 (a)],
carriers in universe `0`): the classes of members of the base on each **positive finite** carrier
`Fin (n + 1)`, and on `ℕ`, in a disjoint union.  Every countable nonempty carrier is in bijection
with exactly one of these, and isomorphic structures have carriers of the same cardinality, so this
type represents the countable members of the base up to isomorphism (the stated target
`WeakSystem.BaseClassesRepresentTarget`).  Correspondence with the printed definitions. -/
abbrev BaseClasses (W : WeakSystem.{w, w', 0} D S) : Type (max wc wc') :=
  (Σ n : ℕ, Quotient (W.baseIsoSetoid E (Fin (n + 1)))) ⊕ Quotient (W.baseIsoSetoid E ℕ)

/-! ### Infinite members: an explicit extra hypothesis -/

/-- **Every member on a countable carrier is infinite.**  Not a field and not a printed condition:
the explicit extra hypothesis of the statements that count only the models coded on `ℕ` (the
lower bound of [AFK26, Theorem 2.25 (a)] in coded form, and [AFK26, Theorem 2.27] in coded form).
Correspondence with the printed definitions. -/
def CountableMembersInfinite : Prop :=
  ∀ (β : SystemLevel) (M : Type v) [Countable M] (G : L.Structure M), G ∈ W.K β M → Infinite M

/-! ### Sentences axiomatizing the base -/

/-- **A sentence axiomatizing the base, on the codes on `ℕ`** ([AFK26, Definitions 2.24 and 2.26],
coded): a code `c` on `ℕ` is a model of `φ` exactly when its structure is in the base.  Only the
models on `ℕ` are seen; the finite models are the subject of `IsBaseSentenceOnCarriers`.  The
instance premises are the relational language and the countability of `L_c` required by
InfinitaryLogic's `ModelsOf`.  Correspondence with the printed definitions. -/
def IsBaseSentence (W : WeakSystem.{w, w', 0} D S) [Lc.IsRelational]
    [Countable (Σ n, Lc.Relations n)] (φ : Lc.Sentenceω) : Prop :=
  ∀ c : StructureSpace Lc, c ∈ ModelsOf φ ↔ W.IsInBase E c.toStructure

/-- **A sentence axiomatizing the base, on all countable nonempty carriers** ([AFK26, Definitions
2.24 and 2.26], with the conventions of [AFK26, §1]): on every countable nonempty carrier in
universe `0`, finite or infinite, `B ⊨ φ` exactly when `B` is in the base.  Correspondence with the
printed definitions. -/
def IsBaseSentenceOnCarriers (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) : Prop :=
  ∀ (M : Type) [Countable M] [Nonempty M] (B : Lc.Structure M),
    @Sentenceω.Realize Lc φ M B ↔ W.IsInBase E B

/-- **From all countable nonempty carriers to the codes on `ℕ`**: `ℕ` is one of the carriers.  A
one-line composition with InfinitaryLogic's `mem_modelsOf_iff_realize`.  Correspondence with the
printed definitions. -/
theorem isBaseSentence_of_isBaseSentenceOnCarriers {W : WeakSystem.{w, w', 0} D S}
    [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)] {φ : Lc.Sentenceω}
    (h : W.IsBaseSentenceOnCarriers E φ) : W.IsBaseSentence E φ :=
  fun c ↦ (mem_modelsOf_iff_realize c φ).trans (h ℕ c.toStructure)

end WeakSystem

end VaughtConjecture.Correspondence

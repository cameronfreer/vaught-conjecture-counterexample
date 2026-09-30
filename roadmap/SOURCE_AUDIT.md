# Source audit and provenance

Date: 29 September 2026. This is a static source audit of the supplied archive. It is not a Lean build, proof-term dependency analysis, or independent verification of the endpoint.

## Input archives

- `vaught-conjecture-refactor-receiving-producer-pruning.zip` — SHA-256 `10ee17bfb3e4f62b6bbbc1dde9d3b0589fc9b2bdfeae1aea6057cd2effbafc5b`.
- `recent-newsimple.zip` — SHA-256 `c2958082f8706f4d903c2618532b6588241203dcc7868176f2a3dbe3ba7b07f7`.
- `vaught-tauceti-roadmap-guide.zip` — SHA-256 `506bfff807f7414d9aa91b5468d71f2e24c6a8c7a36f3217914e91b3093d8e66`.

The integration archive is the authority for current implementation status. The recent notes and old roadmaps are historical comparison material, not additional proved premises. A branch name in an archive filename does not identify a Git commit; no unobserved commit hash is inferred. The archive does supply dependency revisions and the Lean toolchain.

## Method and limits

Inspected source text and the finite-construction, minimal-route, and modular guides; extracted current declarations; computed the transitive graph of local `import` lines. There is no `lean` or `lake` executable and no checked dependency build in this environment. The repository records earlier successful checks, but those checks were not rerun here. The proposed `Suggested.lean` is consequently unelaborated.

## Local import census

- Local modules under `VaughtConjecture/`: **1,208**.
- Preferred endpoint reachable local import closure, including itself: **732**.
- Removing only the import of `GrowthProlongationBoundary` from `ConstructedTerminalCountability` in a simulated graph leaves **730**.
- This is an import-edge simulation, not a patched source, verified build, timing estimate, or proof-dependency reduction.
- `TopGradeStableSpectrum` remains reachable through `NonHollowGrowthProlongation → CapStableModel → NonHollowGrowthReceivingCore → AnchorStable`.
- `GlobalHull`, `FiniteHullPreservation`, `HullCoordinateFormulas`, global stopping applications, and `ConstructedDomainSeparation` are not in the preferred endpoint closure. `FiniteHull` is.

Full machine-readable census: `CURRENT_IMPORT_CENSUS.json`.

## A1. Preferred route and actual endpoint

### `docs/guide/minimal-proof-route.md` — lines 1–62

SHA-256: `8b56a34a63fa67903b0de610e737f27a6bc08025740a7cc8fdbd6c944dc45567`.

```text
1: # The minimal spectrum and thinness route
2: 
3: Updated 2026-09-29. Recommended entry point:
4: [`Knight/ExpansionDomainEndpoint.lean`](../../VaughtConjecture/Knight/ExpansionDomainEndpoint.lean).
5: All four spectrum/perfect-set endpoints there have no producer hypotheses.
6: The sentence and its satisfaction are infinitary; this is not a first-order
7: Vaught claim. Formal verification and independent review of the mathematical
8: interpretation are different obligations.
9: 
10: ## The argument to explain
11: 
12: 1. **Finite construction and receiving.** Legal finite schemes and the coatom
13:    supplier furnish finite extensions. Ordinary receiving gives agreement below
14:    any requested proper cutoff. The constrained LOW and growth constructions
15:    provide the stronger readback needed for terminal classification. Cutoff
16:    receiving alone does not give literal donor tops.
17: 2. **Countable scheduling.** A condition has one finite master tuple and its
18:    type. Its partial realization is the derived face diagram. Absorb every
19:    request's root before deciding the request: exact consistency then makes a
20:    wrong-type answer permanent, including a supported invisible root. Service
21:    and point absorption are countably many cofinal requirements. Mathlib's
22:    `Order.sequenceOfCofinals` supplies the chain, and exact consistency passes
23:    to its union. The exact-family and top-free capped clients share this theorem
24:    but not their different service requirements.
25: 3. **Countable terminal losses.** Count terminal models by countably many
26:    conditions: a globally rigid core of a specified finite type, no rigid core
27:    and eventual top grade `K`, or hollow top-grade growth. Each condition admits
28:    at most one class; non-hollow growth prolongs. Characteristic arity is not
29:    needed in this counting argument. For the
30:    latter, the lawful stable candidate receives every finite cap request, hence
31:    is a model by the general cap-to-model theorem; its literal reduct is the
32:    source. The selected occurrence package is a separate consequence, not a
33:    step of this proof. A class
34:    in the difference between two successive expansion domains is represented
35:    by a terminal model at the lower block. No globally chosen terminal
36:    representative for every class is required.
37: 4. **Countable exceptions and logical comparison.** Domains are decreasing and
38:    continuous at countable limits. Countable successor losses therefore give
39:    countable domain complements. Finite-cover receiving transfers a whole
40:    finite cover in one block, so models in the domain at block `η` agree on
41:    sentences of rank at most `η`. There is no additional `ω` factor here.
42: 5. **Standard descriptive upper bound.** Every sentence has a countable truth
43:    side or a countable false side among isomorphism classes. Invariant sentence
44:    separation rules out a perfect antichain; witnessed Morley counting gives
45:    at most `ℵ₁` classes. This does not identify thinness with cardinality below
46:    the continuum, assume CH, or place an unjustified measurable structure on
47:    the quotient of classes.
48: 6. **Independent lower bound.** The top-free capped scheduler constructs a
49:    terminal model at every countable block. Its base class belongs to that
50:    block's successor loss; distinct losses are disjoint. This injects the
51:    countable ordinals into the classes, without converting arbitrary high-stage
52:    models into terminal ones and without global eventual stopping.
53: 
54: The remaining construction-specific burden is finite receiving and terminal
55: classification, not a bespoke perfect-antichain rank analysis or fair scheduler.
56: The current model-to-cap-receiving direction still needs ordinary receiving;
57: the cap-native structural interfaces do not eliminate that producer.
58: 
59: For the definitions and lemma boundaries of a detailed presentation, see the
60: [modular proof outline](modular-proof-outline.md). It distinguishes proved
61: mathematical reformulations, including global finitary hull geometry, from the
62: optional finite-hull preservation and explicit coordinate-formula exports.
```

### `VaughtConjecture/Knight/ExpansionDomainEndpoint.lean` — lines 7–64

SHA-256: `69213042836977697a7c1dcdf69dd2a2e3cb1cb07afd6c7d455c4558408e20af`.

```text
7: import VaughtConjecture.Knight.ExpansionDomainThinnessCore
8: import VaughtConjecture.Knight.ConstructedTerminalCountability
9: import VaughtConjecture.Knight.ConstructedTerminalLoss
10: 
11: /-! # Spectrum and thinness without global termination
12: 
13: Countable terminal losses and limit continuity give countable exceptions to
14: uniform logical comparison. Standard sentence separation gives thinness, and
15: the witnessed Morley dichotomy gives the `ℵ₁` upper bound. Locally constructed
16: top-free terminal models supply nonempty successor losses and the lower bound.
17: 
18: This is the recommended combined spectrum/thinness entry point. It never needs
19: to prove that every counted class eventually stops. Historical cardinality
20: proofs remain separate; the old perfect-set names delegate here. The theorem
21: is about the repository's infinitary sentence and defined spectrum, not a
22: first-order Vaught statement; mathematical definitional review remains separate.
23: -/
24: 
25: namespace VaughtConjecture.Knight.ExpansionDomainEndpoint
26: 
27: open FirstOrder Language Cardinal Spectrum StoppingRankFiltration
28: 
29: /-- Rank-free thinness, using the uniform finite-cover comparison budget: the library's
30: thinness from single-sentence splits on the class presentation. -/
31: theorem isThinOnNatModels : knightSentence.IsThinOnNatModels :=
32:   SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits knightLang knightSentence
33:     modelClass realizes realizes_modelClass
34:     (ExpansionDomain.sentence_split_countable_uniform
35:       ConstructedSpectrumEndpoint.countableTerminalFibres)
36: 
37: /-- The upper bound is the standard witnessed Morley dichotomy, not a count of
38: canonical stopping expansions. -/
39: theorem natModelSpectrum_le_aleph_one : natModelSpectrum knightSentence ≤ aleph 1 :=
40:   Spectrum.natModelSpectrum_le_aleph_one_of_thin isThinOnNatModels
41: 
42: /-- Exact spectrum from standard thinness counting and locally constructed losses. -/
43: theorem natModelSpectrum_eq_aleph_one : natModelSpectrum knightSentence = aleph 1 := by
44:   apply le_antisymm natModelSpectrum_le_aleph_one
45:   rw [natModelSpectrum_knightSentence]
46:   exact ExpansionDomain.aleph_one_le_classes
47: 
48: /-- The all-countable-carrier spectrum agrees, since there are no finite models. -/
49: theorem allCountableSpectrum_eq_aleph_one : allCountableSpectrum knightSentence = aleph 1 :=
50:   allCountableSpectrum_knightSentence.trans natModelSpectrum_eq_aleph_one
51: 
52: /-- The natural-number perfect-set property fails, independently of global termination. -/
53: theorem not_vaughtConjecturePerfectSetFor : ¬ VaughtConjecturePerfectSetFor knightSentence :=
54:   not_vaughtConjecturePerfectSetFor_of_thin
55:     (by rw [natModelSpectrum_eq_aleph_one]; exact aleph0_lt_aleph_one) isThinOnNatModels
56: 
57: /-- The all-countable perfect-set property fails, with the finite-tier guard explicit. -/
58: theorem not_allCountableVaughtConjecturePerfectSetFor :
59:     ¬ AllCountableVaughtConjecturePerfectSetFor knightSentence :=
60:   not_allCountableVaughtConjecturePerfectSetFor_of_thin
61:     (by rw [allCountableSpectrum_eq_aleph_one]; exact aleph0_lt_aleph_one)
62:     isThinOnNatModels hasNoFiniteModels_knightSentence
63: 
64: end VaughtConjecture.Knight.ExpansionDomainEndpoint
```

## A2. Finite geometry and partial charts

### `VaughtConjecture/AmalgamationPlan/AntiExchange.lean` — lines 1–90

SHA-256: `271f8846354f938e90f82468c3e59c8a6d504767c0bb295f99f7b4455ac356a2`.

```text
1: /-
2: Copyright (c) 2026 Cameron Freer. All rights reserved.
3: Released under Apache 2.0 license as described in the file LICENSE.
4: Authors: Cameron Freer
5: -/
6: import VaughtConjecture.AmalgamationPlan.ConvexGeometry
7: import Mathlib.Order.Closure
8: 
9: /-! # Anti-exchange for finite visible hulls
10: 
11: The closed-set accessibility axiom is equivalent to anti-exchange, not merely
12: intersection closure. Hull is a zero-preserving closure operator on subsets of
13: the finite ambient domain. No ordering or enumeration of that domain is chosen.
14: -/
15: 
16: namespace VaughtConjecture.AmalgamationPlan.Plan
17: 
18: variable {α : Type*} [DecidableEq α]
19: 
20: /-- Anti-exchange, stated at closed sets in the finite ambient domain. -/
21: def HullAntiExchange (A : Finset α) (P : Finset (Finset α)) : Prop :=
22:   ∀ B ∈ P, ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x ∉ B → y ∉ B →
23:     x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B)
24: 
25: /-- Intersection closure and the full face suffice for closed hulls. -/
26: theorem hull_mem_of_inter {A S : Finset α} {P : Finset (Finset α)}
27:     (hA : A ∈ P) (hi : ∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P) : hull A P S ∈ P := by
28:   apply Finset.inf'_induction
29:   · exact fun _ hB _ hC => hi _ hB _ hC
30:   · intro B hB
31:     rcases Finset.mem_insert.mp hB with rfl | hB
32:     · exact hA
33:     · exact (Finset.mem_filter.mp hB).1
34: 
35: theorem IsConvexGeometry.hull_mem {A S : Finset α} {P : Finset (Finset α)}
36:     (hP : IsConvexGeometry A P) : hull A P S ∈ P :=
37:   hull_mem_of_inter hP.domain_mem hP.inter_mem
38: 
39: theorem IsConvexGeometry.hull_eq {A B : Finset α} {P : Finset (Finset α)}
40:     (hP : IsConvexGeometry A P) (hB : B ∈ P) : hull A P B = B :=
41:   Finset.Subset.antisymm (hull_minimal hB (Finset.Subset.refl _))
42:     (subset_hull (hP.bounded B hB))
43: 
44: /-- The standard order-theoretic closure operator on the finite ground set. -/
45: def IsConvexGeometry.closureOperator {A : Finset α} {P : Finset (Finset α)}
46:     (hP : IsConvexGeometry A P) : ClosureOperator {S : Finset α // S ⊆ A} where
47:   toFun S := ⟨hull A P S, hull_subset_domain _ _ _⟩
48:   monotone' _ _ h := hull_mono h
49:   le_closure' S := subset_hull S.property
50:   idempotent' _ := Subtype.ext (hP.hull_eq hP.hull_mem)
51:   IsClosed S := S.val ∈ P
52:   isClosed_iff := ⟨fun h => Subtype.ext (hP.hull_eq h), fun h => by
53:     have he := congrArg Subtype.val h
54:     exact he ▸ hP.hull_mem⟩
55: 
56: theorem IsConvexGeometry.hull_empty {A : Finset α} {P : Finset (Finset α)}
57:     (hP : IsConvexGeometry A P) : hull A P ∅ = ∅ := hP.hull_eq hP.empty_mem
58: 
59: /-- Maximize a closed set omitting both points. Its next one-point extension
60: cannot contain either point if each forces the other. -/
61: theorem IsConvexGeometry.antiExchange {A : Finset α} {P : Finset (Finset α)}
62:     (hP : IsConvexGeometry A P) : HullAntiExchange A P := by
63:   intro B hB x hxA y hyA hxy hxB hyB hx hy
64:   let F := P.filter fun C => B ⊆ C ∧ x ∉ C ∧ y ∉ C
65:   have hinit : B ∈ F := Finset.mem_filter.mpr ⟨hB, Finset.Subset.refl _, hxB, hyB⟩
66:   obtain ⟨C, hC, hmax⟩ := F.exists_max_image Finset.card ⟨B, hinit⟩
67:   obtain ⟨hCP, hBC, hxC, hyC⟩ := Finset.mem_filter.mp hC
68:   obtain ⟨z, _, hzC, hzP⟩ := hP.accessible C hCP (by rintro rfl; exact hxC hxA)
69:   have hzX : z ≠ x := by
70:     rintro rfl
71:     have := hull_minimal hzP (Finset.insert_subset (Finset.mem_insert_self _ _)
72:       (hBC.trans (Finset.subset_insert _ _))) hy
73:     exact hyC ((Finset.mem_insert.mp this).resolve_left (Ne.symm hxy))
74:   have hzY : z ≠ y := by
75:     rintro rfl
76:     have := hull_minimal hzP (Finset.insert_subset (Finset.mem_insert_self _ _)
77:       (hBC.trans (Finset.subset_insert _ _))) hx
78:     exact hxC ((Finset.mem_insert.mp this).resolve_left hxy)
79:   have hm := hmax _ (Finset.mem_filter.mpr ⟨hzP,
80:     hBC.trans (Finset.subset_insert _ _), by simpa [hzX, Ne.symm hzX] using hxC,
81:     by simpa [hzY, Ne.symm hzY] using hyC⟩)
82:   rw [Finset.card_insert_of_notMem hzC] at hm
83:   omega
84: 
85: /-- Conversely, a minimal proper closed enlargement has only one new point:
86: two new points would force one another, contrary to anti-exchange. -/
87: theorem accessible_of_antiExchange {A : Finset α} {P : Finset (Finset α)}
88:     (hb : ∀ B ∈ P, B ⊆ A) (hA : A ∈ P)
89:     (hi : ∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P) (ha : HullAntiExchange A P)
90:     {B : Finset α} (hB : B ∈ P) (hne : B ≠ A) :
```

### `VaughtConjecture/AmalgamationPlan/PairHulls.lean` — lines 1–70

SHA-256: `5d324885e7e8227e434a86d551d4b27a9d3674b4c3042cf468cb076b02a47323`.

```text
1: /-
2: Copyright (c) 2026 Cameron Freer. All rights reserved.
3: Released under Apache 2.0 license as described in the file LICENSE.
4: Authors: Cameron Freer
5: -/
6: import VaughtConjecture.AmalgamationPlan.ConvexGeometry
7: 
8: /-! # Plans are generated by sets of at most two points -/
9: 
10: namespace VaughtConjecture.AmalgamationPlan.Plan
11: 
12: variable {α : Type*} [DecidableEq α]
13: 
14: theorem extremes_hull_subset {A S : Finset α} {P : Finset (Finset α)}
15:     (hS : S ⊆ A) : extremes P (hull A P S) ⊆ S := by
16:   intro x hx
17:   obtain ⟨hxH, hxP⟩ := mem_extremes.mp hx
18:   by_contra hn
19:   have hsub : S ⊆ (hull A P S).erase x := by
20:     intro y hy
21:     exact Finset.mem_erase.mpr ⟨fun he => hn (he ▸ hy), subset_hull hS hy⟩
22:   exact Finset.notMem_erase x _ (hull_minimal hxP hsub hxH)
23: 
24: theorem extremes_singleton {P : Finset (Finset α)} (h0 : ∅ ∈ P) (a : α) :
25:     extremes P {a} = {a} := by
26:   ext x
27:   simp only [mem_extremes, Finset.mem_singleton]
28:   exact ⟨And.left, fun h => ⟨h, by simpa [h] using h0⟩⟩
29: 
30: theorem IsPlan.extremes_card_le_two {A B : Finset α} {P : Finset (Finset α)}
31:     (hP : IsPlan A P) (hB : B ∈ P) : (extremes P B).card ≤ 2 := by
32:   by_cases h : 2 ≤ B.card
33:   · exact (hP.extremes_card hB h).le
34:   · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by omega)
35: 
36: /-- A visible face is exactly the hull of its removable points. -/
37: theorem IsPlan.hull_extremes {A B : Finset α} {P : Finset (Finset α)}
38:     (hP : IsPlan A P) (hB : B ∈ P) : hull A P (extremes P B) = B := by
39:   by_cases h0 : B = ∅
40:   · subst B
41:     simpa [extremes] using hP.hull_eq hP.empty_mem
42:   by_cases h1 : B.card = 1
43:   · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
44:     rw [extremes_singleton hP.empty_mem]
45:     exact hP.hull_eq hB
46:   have h2 : 2 ≤ B.card := by
47:     have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
48:     omega
49:   obtain ⟨a, b, ha, hb, _, hpiv, _, hgen⟩ := (restrict_isPlan hP hB).pivot_pair h2
50:   have hsub : hull A P (extremes P B) ⊆ B := hull_minimal hB (Finset.filter_subset _ _)
51:   apply hgen _ (Finset.mem_inter.mpr ⟨hP.hull_mem, Finset.mem_powerset.mpr hsub⟩)
52:   · apply subset_hull ((Finset.filter_subset _ _).trans (hP.subset_of_mem hB))
53:     exact mem_extremes.mpr ⟨ha, (Finset.mem_inter.mp ((hpiv a ha).mpr (Or.inl rfl))).1⟩
54:   · apply subset_hull ((Finset.filter_subset _ _).trans (hP.subset_of_mem hB))
55:     exact mem_extremes.mpr ⟨hb, (Finset.mem_inter.mp ((hpiv b hb).mpr (Or.inr rfl))).1⟩
56: 
57: /-- Every hull is generated by at most two of the original points. -/
58: theorem IsPlan.exists_small_generator {A S : Finset α} {P : Finset (Finset α)}
59:     (hP : IsPlan A P) (hS : S ⊆ A) :
60:     ∃ T ⊆ S, T.card ≤ 2 ∧ hull A P T = hull A P S :=
61:   ⟨extremes P (hull A P S), extremes_hull_subset hS,
62:     hP.extremes_card_le_two hP.hull_mem, hP.hull_extremes hP.hull_mem⟩
63: 
64: /-- No two different point-pairs (including the empty and singleton cases)
65: have the same hull. -/
66: theorem IsPlan.extremes_hull_small {A S : Finset α} {P : Finset (Finset α)}
67:     (hP : IsPlan A P) (hS : S ⊆ A) (hcard : S.card ≤ 2) :
68:     extremes P (hull A P S) = S := by
69:   by_cases h0 : S = ∅
70:   · subst S
```

### `VaughtConjecture/Knight/Model.lean` — lines 1–92

SHA-256: `6f3cd28ce8f8c291c75388d0a85abc6fe732d362a37558239f8cb486fafbe906`.

```text
1: /-
2: Copyright (c) 2026 Cameron Freer. All rights reserved.
3: Released under Apache 2.0 license as described in the file LICENSE.
4: Authors: Cameron Freer
5: -/
6: import VaughtConjecture.Knight.Tower
7: 
8: /-! # Knight models: the axioms of Def. 3.2.1, clause by clause
9: 
10: Knight's Def. 3.2.1: for `α ≤ ω₁` a limit ordinal, a **model of `S^α`** with (nonempty)
11: domain `M` is a partial function `𝓜` from finite tuples on `M` to `S^α` such that
12: 
13: 1. **(arity)** `𝓜(x)` is undefined when `x` repeats an entry, and `𝓜(x) ∈ S^α_n` when it is
14:    defined on a non-repeating `n`-tuple;
15: 2. **(consistency)** if `𝓜(x) ∈ S^α_n` and `f : m ↪ n`, then `𝓜(x ∘ f) = (S^α f)(𝓜(x))` when
16:    the right side exists, and is undefined when it does not;
17: 3. **(covering)** every non-repeating tuple `a` has some `x` with `a⌢x ∈ dom 𝓜`;
18: 4. **(existential closure)** if `𝓜(x) = p` with `x` an `n`-tuple, and `U` is a subset of the
19:    **cofaces** `(S^α ι_{n,n+1})⁻¹(p)` of one of four kinds — (a)(i) generalised saturation,
20:    (a)(ii) a prescribed `−∞`-pattern, (b) uniformity, (c) high-arity dominance — then there
21:    are `y ∈ M` and `q ∈ U` with `𝓜(x⌢y) = q`.
22: 
23: Here a Knight model is a `TypeTower.Realization` of the Knight tower `knightTower`
24: (`KnightRealization`) satisfying `IsModel`, which transcribes the clauses:
25: 
26: * clause (1) is **automatic** from the encoding: `eval : (Fin n ↪ M) → Option (S α n)` is
27:   only defined on injective tuples and lands in the stage types of the same arity;
28: * clause (2) is `IsExactParentConsistent` (the exact `Option` equality `eval (f.trans t) =
29:   typeMap f q`, decided in #38 — `docs/DESIGN.md` §4);
30: * clause (3) is `IsInitialSegmentCovering` (the paper-literal form; equivalent to the generic
31:   `IsCovering` for Knight realizations by `knightTower_permTotal`, #38);
32: * clause (4) is stated once per family — `genSat`, `bottomPattern`, `uniformity`,
33:   `highGradeDominance` — each saying that **some member of that family** is realized over the
34:   old tuple as a coface (`RealizesSome`): never universal service of an arbitrary coface.  The
35:   four families are `GenSatFamily`, `BottomPatternFamily`, `UniformityFamily`,
36:   `HighGradeDominanceFamily`, with their parameter side conditions stated as hypotheses of the
37:   corresponding clause.
38: 
39: The paper's inclusion `ι_{n,n+1} : n ↪ n+1` is `Fin.castSuccEmb` (definitionally
40: `Fin.castAddEmb 1`, the embedding used by `IsInitialSegmentCovering`), the concatenation
41: `x⌢y` is `snoc`, and the cofaces of `p` are `Coface p`.  In the paper's vocabulary "the arity
42: of a cell" is our **grade** (`docs/TERMINOLOGY.md`), so (c) asks for a cell of grade `n+1`.
43: 
44: Two sibling-only reroutes of Knight-VC are **not** re-imported (`docs/CONCORDANCE.md`):
45: KVC-d23 (the `−∞`-pattern clause restricted to stage-bounded proto-types) — here the pattern
46: source `q'` is any labelling respecting the semantics of `D`, with **no stage bound**, as in
47: the paper; and KVC-d24 (the dominance witness asked for full scope, forgetting its grade) —
48: here the witness has grade `n+1`.
49: 
50: Positive-arity domains and stage types are constructed in `Knight.Domain` (#41 (1/3): mute
51: domains, their one-point extension with the face equation `ExtendsDomain` asks for, and a stage
52: type on every domain, Prop. 4.3.24); `IsModel` is a predicate with no instance in this file —
53: existence of models is #41/#42.  Reduction of a
54: model to a lower limit stage preserves clauses (2) and (3) (`IsModel.consistent_reduct`,
55: `IsModel.covering_reduct`, from the generic lemmas); preservation of the four
56: existential-closure clauses — full modelhood of the reduct, `IsModel.reduct` — is proved in
57: `Knight/ReductModel.lean` (#101; the `−∞`-pattern clause transfers by bountifulness at the
58: cutoff `n + 1`). -/
59: 
60: namespace VaughtConjecture.Knight
61: 
62: open TypeTower
63: open CellScheme.restrictFace (toCell)
64: 
65: universe w
66: 
67: /-! ### Knight realizations, concatenation, cofaces -/
68: 
69: /-- A **Knight realization** at the limit stage `α` on the carrier `M`: a realization of the
70: Knight tower, i.e. a partial labelling of the injective finite tuples of `M` by stage types
71: `S α n` (the raw data of Def. 3.2.1, clause (1) built in). -/
72: abbrev KnightRealization (α : LimitStage) (M : Type w) := knightTower.Realization α M
73: 
74: variable {M : Type w} {n : ℕ}
75: 
76: /-- The concatenation `t⌢y` of an injective `n`-tuple `t` with a point `y` not on it, as an
77: injective `(n+1)`-tuple: `y` sits at the last position (`Fin.snoc`). -/
78: def snoc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) : Fin (n + 1) ↪ M :=
79:   ⟨Fin.snoc (α := fun _ => M) t y, Fin.snoc_injective_of_injective t.injective hy⟩
80: 
81: @[simp] theorem snoc_apply_castSucc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t)
82:     (i : Fin n) : snoc t y hy (Fin.castSucc i) = t i := by
83:   simp [snoc]
84: 
85: @[simp] theorem snoc_apply_last (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) :
86:     snoc t y hy (Fin.last n) = y := by
87:   simp [snoc]
88: 
89: /-- The old tuple is the initial segment of its concatenation: `(t⌢y) ∘ ι_{n,n+1} = t`. -/
90: @[simp] theorem castSuccEmb_trans_snoc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) :
91:     Fin.castSuccEmb.trans (snoc t y hy) = t := by
92:   ext i
```

## A3. Permitted-cap lifting, not lawful cap endomorphisms

### `VaughtConjecture/Knight/CapBallLifting.lean` — lines 7–70

SHA-256: `beb343e94146dad0c6cc97ad75b5cd61fb753a54d00c547bb69ec9dca647b0f4`.

```text
7: 
8: /-! # Bountifulness as lifting cap balls
9: 
10: A cap ball consists of lawful sections with the same capped observation as its
11: centre. Capped lifting says exactly that restriction maps a target ball onto the
12: corresponding source ball. Only permitted caps are asserted to lift. No claim
13: that an arbitrary capped vector is lawful, or that restriction is injective,
14: is used here.
15: -/
16: 
17: set_option autoImplicit false
18: 
19: namespace VaughtConjecture.Knight.CoatomBoundaryExtension
20: 
21: open Transform Value ExtOrd
22: open VaughtConjecture.AmalgamationPlan
23: 
24: variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
25: variable {sem : Semantics D} {I U : Finset ι × ℕ}
26: 
27: /-- Lawful sections with a fixed capped observation, not capped sections. -/
28: def capBall (sem : Semantics D) (I : Finset ι × ℕ)
29:     (q : D.below I → ExtOrd) (γ : ExtOrd) : Set (D.below I → ExtOrd) :=
30:   {r | RespectsSemanticsBelow sem I r ∧ ∀ d, min (r d) γ = min (q d) γ}
31: 
32: /-- The literal restriction map sends every permitted target cap ball onto its
33: source cap ball exactly when the graded pair has capped lifting. -/
34: theorem cappedLift_iff_capBall_image (h : GradedLe I U) :
35:     CappedLift sem h ↔
36:       ∀ (q : D.below U → ExtOrd), RespectsSemanticsBelow sem U q →
37:       ∀ γ, SelfVis U.2 γ →
38:         (fun r => r ∘ CellScheme.below.mono h) '' capBall sem U q γ =
39:           capBall sem I (q ∘ CellScheme.below.mono h) γ := by
40:   constructor
41:   · intro hl q hq γ hγ
42:     apply Set.Subset.antisymm
43:     · rintro _ ⟨r, ⟨hr, hc⟩, rfl⟩
44:       exact ⟨hr.mono h, fun d => hc (CellScheme.below.mono h d)⟩
45:     · intro p hp
46:       obtain ⟨r, hr, hc, hf⟩ := hl p q γ hp.1 hq hγ (fun d => (hp.2 d).symm)
47:       exact ⟨r, ⟨hr, hc⟩, funext hf⟩
48:   · intro him p q γ hp hq hγ hag
49:     have hm : p ∈ capBall sem I (q ∘ CellScheme.below.mono h) γ :=
50:       ⟨hp, fun d => (hag d).symm⟩
51:     rw [← him q hq γ hγ] at hm
52:     obtain ⟨r, ⟨hr, hc⟩, he⟩ := hm
53:     exact ⟨r, hr, hc, fun d => congrFun he d⟩
54: 
55: /-- The ball formulation includes equal indices; bountifulness itself only
56: requires strict pairs. Both formulations retain the target's visibility test. -/
57: theorem isBountiful_iff_capBall_image :
58:     sem.IsBountiful ↔
59:       ∀ I U, I ∈ Plan.gradedPlan D.plan → U ∈ Plan.gradedPlan D.plan →
60:       ∀ h : GradedLe I U, ∀ q, RespectsSemanticsBelow sem U q →
61:       ∀ γ, SelfVis U.2 γ →
62:         (fun r => r ∘ CellScheme.below.mono h) '' capBall sem U q γ =
63:           capBall sem I (q ∘ CellScheme.below.mono h) γ := by
64:   constructor
65:   · intro hb I U hI hU h
66:     exact (cappedLift_iff_capBall_image h).mp (lift_of_bountiful hb hI hU h)
67:   · intro hb I U hI hU h _
68:     exact (cappedLift_iff_capBall_image h).mpr (hb I U hI hU h)
69: 
70: end VaughtConjecture.Knight.CoatomBoundaryExtension
```

## A4. Actual countable language and sentence

### `VaughtConjecture/Knight/Sentence.lean` — lines 7–68

SHA-256: `366ba35997174a9dd2f887686c6bc94aa807a969837c941acbc6cbe61a29a472`.

```text
7: import VaughtConjecture.Spectrum.Sentence
8: import InfinitaryLogic.Lomega1omega.Semantics
9: 
10: /-! # Knight's sentence `T` in `L_{ω₁,ω}` (Def. 3.3.1–3.3.4), via `InfinitaryLogic`
11: 
12: Knight, §3.3: the language `L` (Def. 3.3.1) has, for each `n`, one `n`-ary relation symbol
13: `P_p` per stage-`ω` type `p ∈ S^ω_n`; the sentence `T` (Def. 3.3.3) says that the relations
14: `P_p` describe a model of `S^ω` (Def. 3.2.1, `Knight.Model`): the tuples carry at most one
15: type, types are consistent under restriction, every tuple extends to a typed one, and the four
16: existential-closure families are served.  Prop. 3.3.5 (the countable models of `T` correspond to
17: the countable models of `S^ω`): the sentence-side half — the two directions of the
18: correspondence between `L`-structures and `KnightRealization`s, clause by clause — is here; the
19: isomorphism-class bookkeeping is `Knight/Correspondence.lean` (#43).
20: 
21: **Language** (`knightLang : Language.{0, 1}`): relational, `Relations n := S ω n` (stage `ω`,
22: `omegaStage : LimitStage`), no function symbols; countable (`countable_S_omega`, Prop. 3.1.4
23: at `ω`), as `InfinitaryLogic`'s `StructureSpace` requires.
24: 
25: **Enumeration.**  `L_{ω₁,ω}` conjunctions and disjunctions over the countable parameter spaces
26: of Def. 3.3.3 — arities, stage-`ω` types `S ω n`, embeddings `Fin m ↪ Fin n`, domains
27: `SemScheme (n+1)`, ordinals below `ω` — are `einf`/`esup` (`InfinitaryLogic`) along the
28: enumeration `Encodable.ofCountable` of the (countable) index type: `cinf`/`csup` below, with
29: `realize_cinf`/`realize_csup`.  This replaces Knight-VC's `IFormula` constructors
30: `forallType`/`existsType` over relation symbols (`PORTING.md`).  Clause (a)(ii) is parameterized
31: in the paper by a labelling `q' : D → {−∞} ∪ Ord ∪ {∞}` — **uncountably** many — but the
32: family it requests, `BottomPatternFamily D q'`, depends on `q'` only through its `−∞`-pattern
33: on the finitely many cells of `D^{≤n}`; so the clause is written as a countable conjunction
34: over the **patterns** `π : D^{≤n} → Bool` for which some faithful `q'` extending `p` has pattern
35: `π` (`BottomPatternParam p`, `IsPatternOf`), a faithful re-encoding of the paper's
36: parameterization (`realize_bottomPatternClause` is stated in the paper's `q'` form).
37: 
38: **The sentence.**  One definition per clause — `nonemptyClause` (the carrier is nonempty, Def.
39: 3.2.1's standing convention), `arityClause` (Def. 3.2.1(1): `P_p` holds only on injective
40: tuples), `consistencyClause` (Def. 3.2.1(2), exact: `P_p(x̄) → (P_q(x̄∘f) ⇔ S^ω f (p) = q)`; at
41: `f = id` this is "at most one type per tuple"), `coveringClause` (Def. 3.2.1(3), initial
42: segment), and the four existential-closure clauses `genSatClause`, `bottomPatternClause`,
43: `uniformityClause`, `highGradeDominanceClause` (Def. 3.2.1(4)(a)(i), (a)(ii), (b), (c)), all
44: instances of one shape `ecClause`: `∀ x̄, P_p(x̄) → ⋀_{params} ⋁_{q ∈ U, q a coface of p} ∃ y,
45: P_q(x̄⌢y)` — and `knightSentence`, their conjunction.
46: 
47: **Realization lemmas.**  Each clause has `realize_<clause>`, the semantic condition on an
48: `L`-structure `M` (`Holds p xs` is `P_p(x̄)`); `IsKnightModel M` bundles the eight conditions,
49: and `realize_knightSentence_iff : M ⊨ω knightSentence ↔ IsKnightModel M`.  The correspondence
50: shape: `toRealization M : KnightRealization omegaStage M` (the type of a tuple is the relation
51: holding on it) with `IsKnightModel.isModel_toRealization`, and `structureOf R : knightLang.Structure
52: M` for a realization `R` with `IsModel.isKnightModel`; both round-trip
53: (`toRealization_structureOf_eval`, `holds_structureOf_toRealization`).  Hence every countable
54: model of `T` is (the structure of) a model of `S^ω` and conversely; the isomorphism-class
55: bookkeeping (`isoSetoid`, `codeModel`, `AllCodedIsoClasses`) is `Knight/Correspondence.lean` (#43).
56: 
57: **No finite models.**  `hasNoFiniteModels_knightSentence : HasNoFiniteModels knightSentence`:
58: a structure realizing `T` is a model of `S^ω`, and every model is infinite
59: (`KnightRealization.IsModel.infinite_carrier`: covering labels the empty tuple and
60: existential closure
61: (4)(c) at `γ = 0` adds a fresh point to every labelled tuple) — no domain construction (#41)
62: is involved. -/
63: 
64: namespace VaughtConjecture.Knight
65: 
66: open FirstOrder Language Structure TypeTower
67: open scoped Lomega1omega
68: 
```

## A5. Generic scheduler and finite/infinite separation

### `VaughtConjecture/TypeTower/FiniteMasterScheduler.lean` — lines 7–95

SHA-256: `403abc273d57b3d32d8ab7241dfa4e2da56d673f902c8065dfbcf2236eadac42`.

```text
7: import VaughtConjecture.TypeTower.ChainUnion
8: import Mathlib.Order.Ideal
9: import Mathlib.Data.Countable.Basic
10: 
11: /-! # Finite-master scheduling by countable dense sets
12: 
13: There are two finite obligations: absorb a carrier point, and serve an applicable
14: rooted task. Before deciding a task, absorb its entire root. Its option is then fixed
15: forever, so rejection is permanent and service needs no arbitrarily-late repetition.
16: Mathlib's `Order.sequenceOfCofinals` supplies the only recursion.
17: 
18: The countable alphabet consists of **task codes**, not all answer families. `RootedTask`
19: allows any upward-persistent service predicate; in the applications it is a finite
20: coface evaluation in an exact family, or an exact-scheme capped donor observation.
21: State invariants are carried by the arbitrary state type `S`; neither the state space
22: nor the tower's types need be countable. The theorem also covers empty alphabets and
23: empty carriers: `Encodable.decode` provides the idle steps automatically.
24: -/
25: 
26: namespace VaughtConjecture.TypeTower
27: 
28: universe u v w z z'
29: variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}
30: 
31: /-- A rooted obligation, with service persistent under positive realization extension. -/
32: structure RootedTask (T : TypeTower.{u} Λ) (α : Λ) (M : Type w) where
33:   n : ℕ
34:   root : Fin n ↪ M
35:   base : T.Ty α n
36:   Served : T.Realization α M → Prop
37:   mono : ∀ {A B}, A.Extends B → Served A → Served B
38: 
39: namespace FiniteMasterScheduler
40: 
41: variable {S : Type z} (master : S → FiniteMaster T α M)
42: 
43: /-- Supported and either permanently rejected or already served. -/
44: def Resolved (r : RootedTask T α M) (s : S) : Prop :=
45:   (master s).Supported r.root ∧
46:     ((master s).chart.eval r.root ≠ some r.base ∨ r.Served (master s).chart)
47: 
48: theorem resolved_mono {r : RootedTask T α M} {s t : S}
49:     (h : master s ≤ master t) (hr : Resolved master r s) : Resolved master r t := by
50:   refine ⟨h.supported hr.1, ?_⟩
51:   rcases hr.2 with hn | hs
52:   · exact Or.inl (by rwa [h.eval_eq hr.1])
53:   · exact Or.inr (r.mono ((master s).extends_iff (master t) |>.mp h) hs)
54: 
55: variable
56:   (absorb : ∀ (s : S) (x : M), ∃ t, master s ≤ master t ∧ x ∈ Set.range (master t).tuple)
57: 
58: include absorb
59: 
60: /-- Finitely many absorptions decide all coordinates of a root, not its visibility. -/
61: theorem absorb_finset (s : S) (F : Finset M) :
62:     ∃ t, master s ≤ master t ∧ ∀ x ∈ F, x ∈ Set.range (master t).tuple := by
63:   classical
64:   induction F using Finset.induction_on with
65:   | empty => exact ⟨s, le_rfl, by simp⟩
66:   | @insert x F hx ih =>
67:     obtain ⟨t, hst, ht⟩ := ih
68:     obtain ⟨r, htr, hr⟩ := absorb t x
69:     refine ⟨r, hst.trans htr, ?_⟩
70:     intro y hy
71:     rcases Finset.mem_insert.mp hy with rfl | hy
72:     · exact hr
73:     · exact htr.range_mono (ht y hy)
74: 
75: theorem resolve (s : S) (r : RootedTask T α M)
76:     (serve : ∀ s, (master s).chart.eval r.root = some r.base →
77:       ∃ t, master s ≤ master t ∧ r.Served (master t).chart) :
78:     ∃ t, master s ≤ master t ∧ Resolved master r t := by
79:   classical
80:   obtain ⟨t, hst, ht⟩ := absorb_finset master absorb s (Finset.univ.image r.root)
81:   have hsupp : (master t).Supported r.root :=
82:     ((master t).supported_iff r.root).mpr fun i => ht _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
83:   by_cases hp : (master t).chart.eval r.root = some r.base
84:   · obtain ⟨q, htq, hq⟩ := serve t hp
85:     exact ⟨q, hst.trans htq, htq.supported hsupp, Or.inr hq⟩
86:   · exact ⟨t, hst, hsupp, Or.inl hp⟩
87: 
88: /-- Countable dense-set scheduling. Each request is resolved once; all points are absorbed. -/
89: theorem exists_chain {I : Type z'} [Countable I] [Countable M]
90:     (task : I → RootedTask T α M)
91:     (serve : ∀ (s : S) (i : I), (master s).chart.eval (task i).root = some (task i).base →
92:       ∃ t, master s ≤ master t ∧ (task i).Served (master t).chart)
93:     (seed : S) :
94:     ∃ A : ℕ → S, A 0 = seed ∧ Monotone (master ∘ A) ∧
95:       (∀ x, ∃ k, x ∈ Set.range (master (A k)).tuple) ∧
```

### `docs/notes/finite-construction-core.md` — lines 1–90

SHA-256: `65ff2d5c913659d4defa189c74c720f18877e4b9d27cde164e3337571fc87110`.

```text
1: # Finite construction below scheduling
2: 
3: Date: 2026-09-28 (UTC)
4: 
5: Branch: `refactor/finite-construction-core`
6: 
7: Base: `0fa3f68074efdaf479b47980c2e4d0b0c2e46e3f`
8: 
9: ## Result and boundary
10: 
11: The top-free finite supplier no longer imports `FixedHeightHenkin`,
12: `RequestCensus`, or a chain-union construction. The full top-free existence
13: module also no longer imports the historical Henkin/census modules. Its shared
14: countable dense-set scheduler and generic chain union remain legitimate dependencies.
15: 
16: This is an extraction, not a stronger extension theorem. Rows, catalogues, model
17: predicates, supplier hypotheses, public theorem names and scheduler endpoints are
18: unchanged. The exact-family scheduler still uses its request census.
19: 
20: ## Finite interface map
21: 
22: All moved declarations retain their existing namespaces and names.
23: 
24: | Module | Contents |
25: | --- | --- |
26: | `FiniteTupleGeometry` | Extension embeddings, arbitrary padding, append/factor equations. |
27: | `FiniteCofaceSupply` | Prescribed-coface supply and its exact-pair consequence. |
28: | `FiniteRequestData` | Finite bottom patterns and elementary tuple/cut countability, without a census. |
29: | `FiniteFamilySupply` | Family requests, band supply, joint pinned supply and padded canonical supply. |
30: | `FiniteRequestSupply` | Existential request-local supply and the choice equivalence with canonical supply. |
31: | `CoatomSupplyAdapters` | Finite coatom-to-prescribed/family supply adapters, without model existence. |
32: | `FinitePartialState` | Finite partial diagrams, fresh blocks and finite master installation helpers. |
33: | `FiniteMasterInstall` | The unchanged padded finite installation theorem. |
34: | `FiniteMasterState` | Master-chart normal form, historical state adapters and initialization. |
35: | `FiniteMasterSteps` | Finite service and absorption, including a specified fresh point. |
36: 
37: `TypeTower.RealizationExtension` now contains the elementary extension relation,
38: so finite charts no longer need to import its infinite-union consumer.
39: `FixedHeightChain` separately exposes the existing Knight chain-union adapters.
40: 
41: The old paths `FixedHeightHenkin`, `HenkinMasterSteps`,
42: `RequestLocalHenkin`, `CoatomHenkinBridge`, `RequestCensus`, and
43: `TypeTower.ChainUnion` reexport the relocated names. Their remaining
44: census-dependent or infinite applications stay in those layers.
45: 
46: The new `FixedHeight.initialSegmentCover_of_mastered` states the finite
47: covering conclusion without packaging it as a census `Services` assertion.
48: The old `services_covering_of_mastered` is its compatibility corollary.
49: The historical top-free run-covering proof now uses the finite conclusion directly.
50: 
51: ## Preserved distinctions
52: 
53: - A prescribed coface is not merely a member of a requested family. Both contracts
54:   remain separate, and the band producer is still needed by the family adapter.
55: - Padding is arbitrary; no zero-padding assumption was added.
56: - `exists_fresh_block_with` and `exists_serviceState_at` retain the designated
57:   fresh coordinate, not just an existentially chosen unrelated point.
58: - The master is retained literally. Supported invisible faces remain invisible;
59:   an unsupported tuple is not identified with an invisible supported one.
60: - Empty masters and all existing `RunState` interfaces remain available.
61: 
62: ## Import measurements
63: 
64: Counts below are reachable local `VaughtConjecture.*` modules, including the
65: named root, before and after this extraction. They are not proof-dependency
66: counts, build-time measurements or counts of external library modules.
67: 
68: | Root | Base | Extracted |
69: | --- | ---: | ---: |
70: | `CoatomFaceLift` | 31 | 21 |
71: | `MasterChart` | 27 | 16 |
72: | `TopFreePinnedExtension` | 295 | 294 |
73: | `TopFreeCapHenkin` | 306 | 310 |
74: 
75: The full top-free closure has more files because several large modules were
76: split. The substantive boundary improvement is exclusion of historical
77: scheduling: `FixedHeightHenkin`, `RequestCensus`, and
78: `HenkinMasterSteps` disappear from that closure. The pinned finite closure also
79: loses `TypeTower.ChainUnion`. Other rank-related imports reachable through the
80: finite coatom producer were not claimed to disappear.
81: 
82: Three compiled import guards test these boundaries independently:
83: 
84: - `AuditFiniteConstructionImports`: finite coatom adapters and finite installers
85:   exclude both historical scheduling and generic infinite union/scheduling.
86: - `AuditPinnedConstructionImports`: the actual constructed top-free pinned
87:   supplier excludes those dependencies.
88: - `AuditTopFreeConstructionImports`: full top-free existence excludes historical
89:   scheduling, while allowing the shared generic scheduler.
90: 
```

## A6. Countably many conditions replace characteristic-based counting

### `VaughtConjecture/Knight/TopGradeTerminalCounting.lean` — lines 7–143

SHA-256: `9f6c3b457beb08740ea7b04f14ab64c11982b46cf8b45b14a98992495dd98627`.

```text
7: import VaughtConjecture.Knight.TopSupportRigidCore
8: import VaughtConjecture.Knight.TopGradeDichotomy
9: import VaughtConjecture.Knight.CountableTerminalFibres
10: 
11: /-! # Counting terminal classes directly from top-grade behaviour
12: 
13: At a countable stage the models are covered by countably many conditions, each met by
14: at most one isomorphism class:
15: 
16: * an actual globally rigid core of a given finite type (rigid-core comparison);
17: * no globally rigid core, and top grade eventually a given `K` (cap-native residual
18:   comparison, which consumes the coinitial top-grade tail itself);
19: * hollow top-grade growth (hollow-growth comparison).
20: 
21: The top-grade dichotomy places every model without a core in the second or third
22: condition. Eventual top grade zero leaves no actual top cell, so the empty tuple is then a
23: globally rigid core; the second condition therefore only occurs with `K > 0`.
24: 
25: No characteristic arity, stable spectrum, or characteristic-based growth predicate on
26: terminal classes is used. Growth prolongation and hollow-growth comparison are consumed
27: as hypotheses here and supplied in `ConstructedTerminalCountability`.
28: -/
29: 
30: set_option autoImplicit false
31: namespace VaughtConjecture.Knight.TopGradeTerminalCounting
32: open TypeTower StageType KnightRealization Value ExtOrd TopSupport Cardinal
33: noncomputable section
34: universe w
35: variable {α : LimitStage} {M : Type w} {W : KnightRealization α M}
36: 
37: /-- Countably many conditions, each met by at most one member of a family and jointly
38: covering it, make the family countable. -/
39: theorem countable_of_cover {ι κ : Type*} [Countable κ] (P : κ → ι → Prop)
40:     (hsub : ∀ c i j, P c i → P c j → i = j) (hcover : ∀ i, ∃ c, P c i) : Countable ι := by
41:   choose c hc using hcover
42:   refine Function.Injective.countable (f := c) fun i j h => hsub (c i) i j (hc i) ?_
43:   rw [h]
44:   exact hc j
45: 
46: /-- **Eventual top grade zero gives a rigid core**: every actual top grade is then zero,
47: so no actual cover has a top cell, and every tuple (in particular the empty one) is a
48: globally rigid core. -/
49: theorem rigidCore_of_isCoinitial_zero
50:     (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = 0})
51:     {k : ℕ} (B : Fin k ↪ M) : TopSupportRigidCore.RigidCore W B := by
52:   intro m C c hc e he H hH ht
53:   apply Set.Subset.antisymm hH.subset
54:   intro d hd
55:   have hg : c.scheme.scheme.grade d ≤ 0 :=
56:     (le_csSup c.topGrades_bddAbove (grade_mem_topGrades (mem_topSet.mp hd))).trans
57:       (topGrade_le_of_isCoinitial hcoin ⟨m, C, c, hc⟩)
58:   exact ((c.scheme.scheme.grade_pos d).ne' (Nat.le_zero.mp hg)).elim
59: 
60: /-- Without a globally rigid core, an eventual top grade is positive. -/
61: theorem pos_of_isCoinitial {K : ℕ}
62:     (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K})
63:     (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B) : 0 < K := by
64:   rcases Nat.eq_zero_or_pos K with rfl | hK
65:   · exact (hres (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
66:       (rigidCore_of_isCoinitial_zero hcoin _)).elim
67:   · exact hK
68: 
69: /-- **At most one coreless class per eventual top grade**: two countable models at the
70: same stage without globally rigid cores, whose top grades are eventually the same `K`,
71: are isomorphic. Positivity of `K` is derived, not assumed. -/
72: theorem nonempty_iso_of_isCoinitial {M₁ M₂ : Type w} [Countable M₁] [Countable M₂]
73:     {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
74:     (hM₁ : W₁.IsModel) (hM₂ : W₂.IsModel) {K : ℕ}
75:     (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
76:     (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
77:     (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
78:     (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B) :
79:     Nonempty (W₁.Iso W₂) := by
80:   have := hM₁.nonempty
81:   have := hM₂.nonempty
82:   exact LowOnlyResidualClassification.nonempty_iso_of_receiving hM₁.consistent hM₁.covering
83:     (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
84:     (OrdinaryModelReceiving.finiteCutReceiving hM₂) hcoin₁ hcoin₂
85:     (pos_of_isCoinitial hcoin₁ hres₁) hres₁ hres₂
86: 
87: /-- **Counting by top-grade conditions.** At a countable stage, a pairwise non-isomorphic
88: family of countable models is countable when its growth members are hollow and hollow
89: growth members compare. The cover: an actual rigid core of a given finite type; no rigid
90: core and eventual top grade a given `K`; hollow growth. -/
91: theorem countable {ι : Type*} (hα : α.1.card ≤ Cardinal.aleph0)
92:     {N : ι → Type w} [∀ i, Countable (N i)]
93:     (W : ∀ i, KnightRealization α (N i)) (hW : ∀ i, (W i).IsModel)
94:     (hhollow : ∀ i, (W i).HasTopGradeGrowth → (W i).IsHollow)
95:     (hcompare : ∀ i j, (W i).HasTopGradeGrowth → (W j).HasTopGradeGrowth →
96:       (W i).IsHollow → (W j).IsHollow → Nonempty ((W i).Iso (W j)))
97:     (hanti : ∀ i j, i ≠ j → IsEmpty ((W i).Iso (W j))) : Countable ι := by
98:   have : ∀ n, Countable (S α.1 n) := fun n => StageType.countable_S hα n
99:   have heq : ∀ i j, Nonempty ((W i).Iso (W j)) → i = j := by
100:     intro i j h
101:     by_contra hne
102:     exact (hanti i j hne).false h.some
103:   refine countable_of_cover (κ := (Σ n : ℕ, S α.1 n) ⊕ ℕ ⊕ Unit)
104:     (Sum.elim
105:       (fun p i => ∃ B : Fin p.1 ↪ N i,
106:         (W i).eval B = some p.2 ∧ TopSupportRigidCore.RigidCore (W i) B)
107:       (Sum.elim
108:         (fun K i => (∀ {k : ℕ} (B : Fin k ↪ N i), ¬ TopSupportRigidCore.RigidCore (W i) B) ∧
109:           KnightRealization.IsCoinitial {x : (W i).LabelledExt | x.type.topGrade = K})
110:         (fun _ i => (W i).HasTopGradeGrowth ∧ (W i).IsHollow))) ?_ ?_
111:   · rintro (⟨k, p⟩ | K | ⟨⟩) i j hi hj
112:     · obtain ⟨B₁, h₁, r₁⟩ := hi
113:       obtain ⟨B₂, h₂, r₂⟩ := hj
114:       exact heq i j (TopSupportRigidCore.nonempty_iso_of_rigidCores (hW i) (hW j) h₁ h₂ r₁ r₂)
115:     · exact heq i j (nonempty_iso_of_isCoinitial (hW i) (hW j) hi.2 hj.2 hi.1 hj.1)
116:     · exact heq i j (hcompare i j hi.1 hj.1 hi.2 hj.2)
117:   · intro i
118:     by_cases hcore : ∃ (k : ℕ) (B : Fin k ↪ N i), TopSupportRigidCore.RigidCore (W i) B
119:     · obtain ⟨k, B, b, hb, hr⟩ := TopSupportRigidCore.exists_labelled_core (hW i) hcore
120:       exact ⟨.inl ⟨k, b⟩, B, hb, hr⟩
121:     · rcases (hW i).hasTopGradeGrowth_or_coinitial_constant with hg | ⟨K, hK⟩
122:       · exact ⟨.inr (.inr ()), hg, hhollow i hg⟩
123:       · exact ⟨.inr (.inl K), fun B hB => hcore ⟨_, B, hB⟩, hK⟩
124: 
125: /-- **Terminal countability from top-grade behaviour.** At a countable block, the terminal
126: classes are countable once non-hollow growth prolongs and hollow growth models compare.
127: Terminality turns the prolongation into hollowness of every growth representative. -/
128: theorem countable_terminalClass {ρ : Ordinal.{0}} (hρ : ρ < (aleph 1).ord)
129:     (hprolong : ∀ W : TerminalModel ρ, ¬ W.1.IsHollow → W.1.HasTopGradeGrowth →
130:       W.1.ProlongsToIn IsModelClass (blockStage_le_succ ρ))
131:     (hcompare : ∀ W V : TerminalModel ρ,
132:       W.1.HasTopGradeGrowth → V.1.HasTopGradeGrowth → W.1.IsHollow → V.1.IsHollow →
133:         Nonempty (W.1.Iso V.1)) : Countable (TerminalClass ρ) := by
134:   apply countable
135:     (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hρ)))
136:     (fun q : TerminalClass ρ => q.out.1) (fun q => q.out.2.1)
137:   · intro q hg
138:     by_contra hn
139:     exact q.out.2.2 (hprolong q.out hn hg)
140:   · intro q r
141:     exact hcompare q.out r.out
142:   · intro q r hne
143:     exact ⟨fun e => hne (Quotient.out_equiv_out.mp ⟨e⟩)⟩
```

### `VaughtConjecture/Knight/ConstructedTerminalCountability.lean` — lines 7–47

SHA-256: `42bf2d0a4b7e0cf55c70e65627f34a5df68948281c868373ce9aec6ffd6e1ded`.

```text
7: import VaughtConjecture.Knight.HollowGrowthComparison
8: import VaughtConjecture.Knight.TopGradeTerminalCounting
9: import VaughtConjecture.Knight.BlockSuccessor
10: import VaughtConjecture.Knight.GrowthProlongationBoundary
11: 
12: /-! # Constructed terminal countability, before the spectrum applications
13: 
14: Non-hollow growth prolongs; hollow growth models compare. Together with the
15: top-grade count of `TopGradeTerminalCounting` (rigid cores, eventual top grade,
16: hollow growth), these give countable terminal fibres. The count consumes the
17: coinitial top-grade tail directly; it does not pass through characteristic.
18: Neither cofinal high-stage existence nor an exact-cardinality conclusion is an
19: input. Both cardinality and expansion-domain thinness consume this producer.
20: 
21: The historical namespace and theorem names are retained. This separates the
22: producer from the cardinality application, not from all rank-related imports
23: inside the existing classification infrastructure.
24: -/
25: 
26: set_option autoImplicit false
27: namespace VaughtConjecture.Knight.ConstructedSpectrumEndpoint
28: open TypeTower KnightRealization
29: universe w
30: 
31: /-- The constructed non-hollow growth prolongation producer at every block stage. -/
32: theorem growthAnchorProlongationAt {M : Type w} {ρ : Ordinal.{0}}
33:     {W : KnightRealization (blockStage ρ) M} (hW : W.IsModel) :
34:     GrowthAnchorProlongationAt W := by
35:   rintro ⟨hh, hg⟩
36:   rw [prolongsToIn_isModelClass_iff_on]
37:   exact NonHollowGrowthReceiving.prolongsToOnIn_of_eq_nextBlock hW hh hg
38:     (blockStage_succ_eq_nextBlock ρ) _
39: 
40: /-- Every countable-rank terminal fibre has countably many isomorphism classes. -/
41: theorem countableTerminalFibres : CountableTerminalFibres :=
42:   TopGradeTerminalCounting.countableTerminalFibres_of_growth_results
43:     (fun _ _ W hh hg => growthAnchorProlongationAt W.2.1 ⟨hh, hg⟩)
44:     (fun _ _ W V hgW hgV hhW hhV =>
45:       HollowGrowth.nonempty_iso W.2.1 V.2.1 hgW hgV hhW hhV)
46: 
47: end VaughtConjecture.Knight.ConstructedSpectrumEndpoint
```

## A7. Structural stable lift, hollowness, and cap-native continuation

### `VaughtConjecture/Knight/StableLift.lean` — lines 7–14

SHA-256: `7a49f0ff20e1a1964ca81ab13e59d865d645ccc4237ed8146f2319304c412046`.

```text
7: 
8: /-! # Stable lift: compatibility facade
9: 
10: `StableLiftCore` constructs the lawful, consistent, covering stable realization.
11: `StableOccurrenceSupply` states the separate band/grade interfaces.
12: `StableOccurrenceModel` retains their modelhood sufficiency and prolongation results.
13: All existing names, signatures and definitional wrappers remain available here.
14: -/
```

### `VaughtConjecture/Knight/AnchorStable.lean` — lines 166–206

SHA-256: `561a56bf47f9899660d3b641054a11b2aad7177525ccc8368388274cec442658`.

```text
166: 
167: theorem stableValue_le_of_anchor (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
168:     (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {K' : ℕ}
169:     (h : R.IsInfinityAnchor t p Xi K') : R.stableValue t p Xi ≤ ofOrd (α.1 + K') := by
170:   obtain ⟨j, hj, hs⟩ := exists_stableValue_of_anchor hM hpt h
171:   rw [hs, ofOrd_le_ofOrd]
172:   exact add_le_add_right (Nat.cast_le.mpr hj) _
173: 
174: /-! ## The equivalences -/
175: 
176: /-- **Anchors are exactly the finite stable top values.** -/
177: theorem hasInfinityAnchor_iff_exists_finite_stable (hM : R.IsModel) :
178:     R.HasInfinityAnchor ↔ ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
179:       ∃ (Xi : Cell p.scheme.scheme) (j : ℕ), p.label Xi = ⊤ ∧
180:         R.stableValue t p Xi = ofOrd (α.1 + j) := by
181:   constructor
182:   · rintro ⟨n, t, p, hpt, Xi, K', h⟩
183:     obtain ⟨j, -, hs⟩ := exists_stableValue_of_anchor hM hpt h
184:     exact ⟨n, t, p, hpt, Xi, j, h.1, hs⟩
185:   · rintro ⟨n, t, p, hpt, Xi, j, hXi, hs⟩
186:     exact ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt hXi hs⟩
187: 
188: /-- **Hollowness is exactly stable-label fixedness.** -/
189: theorem isHollow_iff_stable_identity (hM : R.IsModel) :
190:     R.IsHollow ↔ ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
191:       ∀ Xi : Cell p.scheme.scheme, R.stableValue t p Xi = p.label Xi := by
192:   constructor
193:   · intro hh n t p hpt Xi
194:     exact stableValue_eq_label_of_hollow hM hh hpt Xi
195:   · rintro hid ⟨n, t, p, hpt, Xi, K', h⟩
196:     obtain ⟨j, -, hs⟩ := exists_stableValue_of_anchor hM hpt h
197:     rw [hid t p hpt Xi, h.1] at hs
198:     exact ofOrd_ne_top _ hs.symm
199: 
200: /-! ## The sharp threshold under top-grade growth -/
201: 
202: /-- **Under top-grade growth, an anchor at `K'` with stable value `α + j` has `j < K'`.** -/
203: theorem lt_of_anchor_of_growth (hM : R.IsModel) (hg : R.HasTopGradeGrowth) {n : ℕ}
204:     {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme}
205:     {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') {j : ℕ}
206:     (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) : j < K' := by
```

### `VaughtConjecture/Knight/CapStableModel.lean` — lines 7–56

SHA-256: `2f8d7dc1e62aa27119f776f4495b99d4437ccac3ba22602c6252a0b36202603e`.

```text
7: import VaughtConjecture.Knight.NonHollowGrowthReceivingCore
8: 
9: /-! # Stable modelhood through cap receiving
10: 
11: The source is a model; the stable candidate is only known consistent and covering.
12: All-donor positive-root receiving supplies its cap requests. Empty roots are
13: completed by finite singleton attachment, then the four old model clauses follow.
14: This is the modelhood producer used by `NonHollowGrowthProlongation`; the
15: selected-family occurrence-package route remains a separate application.
16: -/
17: 
18: namespace VaughtConjecture.Knight.CapStableModel
19: open TypeTower StageType KnightRealization Value ExtOrd
20: universe w
21: variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
22: 
23: theorem finiteCutReceiving (hM : W.IsModel) (hh : ¬ W.IsHollow)
24:     (hg : W.HasTopGradeGrowth) : FiniteCutReceiving (stableLift hM) := by
25:   apply FiniteCutReceiving.of_positive hM.nonempty
26:     (stableLiftOf_consistent hM.consistent hM.covering)
27:     (stableLiftOf_covering hM.consistent hM.covering)
28:   intro n hn t p hp q hqp δ hδ hδα
29:   obtain ⟨p₀, hp₀, rfl⟩ := stableLift_eval_eq_some hM hp
30:   obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.nextBlock.1 := by
31:     rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
32:     · exact False.elim (lt_irrefl _ hδ)
33:     · exact False.elim ((not_lt_of_ge le_top) hδα)
34:     · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
35:   obtain ⟨y, hy, s, hs, he, hproper, htop⟩ :=
36:     NonHollowGrowthReceiving.receives_positive hM hh hg hn t p₀ hp₀ q hqp ν hν
37:   refine ⟨y, hy, stableLiftType hM _ s hs, stableLift_eval_some hM hs, he.symm, ?_⟩
38:   intro d
39:   change min (W.stableValue (snoc t y hy) s d) (ofOrd ν) =
40:     min (q.label (SemScheme.castCell he.symm d)) (ofOrd ν)
41:   by_cases hd : q.label (SemScheme.castCell he.symm d) = ⊤
42:   · have hh := htop (SemScheme.castCell he.symm d) hd
43:     rw [hd, min_eq_right le_top]
44:     exact min_eq_right hh.le
45:   · have hh := hproper (SemScheme.castCell he.symm d) hd
46:     exact congrArg (fun x => min x (ofOrd ν)) hh
47: 
48: /-- Alternative constructed stable modelhood, without assuming the stable candidate
49: is a model or using its occurrence package as an input. -/
50: theorem isModel (hM : W.IsModel) (hh : ¬ W.IsHollow) (hg : W.HasTopGradeGrowth) :
51:     (stableLift hM).IsModel :=
52:   FiniteCutReceiving.isModel (finiteCutReceiving hM hh hg) hM.nonempty
53:     (stableLiftOf_consistent hM.consistent hM.covering)
54:     (stableLiftOf_covering hM.consistent hM.covering)
55: 
56: end VaughtConjecture.Knight.CapStableModel
```

### `VaughtConjecture/Knight/NonHollowGrowthProlongation.lean` — lines 7–47

SHA-256: `2cc0314820134a49a6d716a746862ff0075dc206369fcb8ed038c4c2c5876390`.

```text
7: 
8: /-! # Non-hollow growth prolongs through cap-native stable modelhood
9: 
10: The stable candidate is consistent and covering before it is known to be a
11: model. Positive-root stable receiving supplies cap requests; finite attachment
12: handles the empty root. The general cap-to-model theorem then supplies modelhood.
13: The literal stable reduct equation gives an actual next-block expansion on the
14: same carrier, without passing through the selected occurrence package.
15: 
16: The historical theorem names are retained and reexported by
17: `NonHollowGrowthReceiving`, which keeps the optional selected-donor application.
18: -/
19: 
20: set_option autoImplicit false
21: namespace VaughtConjecture.Knight.NonHollowGrowthReceiving
22: open TypeTower KnightRealization
23: universe w
24: variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
25: 
26: /-- Modelhood of the canonical stable lift from constructed cap receiving,
27: without assuming stable modelhood or an occurrence supply. -/
28: theorem stableLift_isModel (hM : W.IsModel) (hh : ¬ W.IsHollow)
29:     (hg : W.HasTopGradeGrowth) : (KnightRealization.stableLift hM).IsModel :=
30:   CapStableModel.isModel hM hh hg
31: 
32: /-- An actual next-block model on the same carrier, reducing literally to
33: the original non-hollow growth model. -/
34: theorem exists_nextBlock_model (hM : W.IsModel) (hh : ¬ W.IsHollow)
35:     (hg : W.HasTopGradeGrowth) :
36:     ∃ V : KnightRealization α.nextBlock M, V.IsModel ∧ V.reduct α.le_nextBlock = W :=
37:   ⟨KnightRealization.stableLift hM, stableLift_isModel hM hh hg, stableLift_reduct hM⟩
38: 
39: /-- The same expansion at any target equal to the next block; the stage
40: inequality proof does not affect the literal reduct equation. -/
41: theorem prolongsToOnIn_of_eq_nextBlock (hM : W.IsModel) (hh : ¬ W.IsHollow)
42:     (hg : W.HasTopGradeGrowth) {β : LimitStage} (hβ : β = α.nextBlock)
43:     (hle : α ≤ β) : W.ProlongsToOnIn IsModelClass hle := by
44:   subst β
45:   exact exists_nextBlock_model hM hh hg
46: 
47: end VaughtConjecture.Knight.NonHollowGrowthReceiving
```

## A8. Expansion domains and one-block comparison

### `VaughtConjecture/Knight/ExpansionDomain.lean` — lines 7–164

SHA-256: `7b4edbc13799bdd0e419c58198e7e2d7c93325dfd30369c6e8c1022bcf3bfac2`.

```text
7: import VaughtConjecture.Knight.LimitExpansion
8: import VaughtConjecture.Knight.ProlongationNormalization
9: import VaughtConjecture.Knight.CountableTerminalFibres
10: import VaughtConjecture.Knight.ClassTruth
11: import VaughtConjecture.Knight.OneBlockComparison
12: 
13: /-! # Expansion domains: countable fixed-stage exceptions without stopping ranks
14: 
15: `domain ξ` is the set of counted isomorphism classes admitting a model expansion to block
16: `ξ`.  It is defined by expansion **existence**, not by the stopping rank, and the three facts
17: below use no stopping rank, no termination theorem, and no canonical stopping expansion:
18: 
19: * **Successor losses are countable** (`loss_countable`): any expansion witnessing membership
20:   in `domain ξ` of a class outside `domain (ξ + 1)` is terminal, so the loss lies in the image
21:   of the terminal classes at block `ξ` (`loss_subset_range`), countable by the supplied
22:   terminal-fibre countability.  No canonical or unique expansion is chosen.
23: * **No loss at a countable limit** (`iInter_subset_domain`): the countable-limit expansion
24:   theorem `exists_model_at_limit_of_forall_lt`.
25: * **Fixed-stage complements are countable** (`compl_countable`): the generic
26:   `CountableLoss.compl_countable_of_loss`.
27: 
28: With the one-block readback hypothesis, classes in `domain (ω · η)` agree on every sentence of
29: quantifier rank at most `η` (`realizes_iff_of_mem_domain`), so every sentence has a countable
30: truth side (`sentence_split_countable`).  Terminal countability and receiving are explicit
31: hypotheses here; `ExpansionDomainThinness` discharges them.  The existing rank filtration is
32: untouched: under termination, `domain ξ = {q | ξ ≤ knightNatStopRank q}`, but that
33: identification is not used. -/
34: 
35: namespace VaughtConjecture.Knight.ExpansionDomain
36: 
37: open TypeTower FirstOrder Language KnightRealization Cardinal StoppingRankFiltration
38: 
39: /-- **The expansion domain at block `ξ`**: the counted classes admitting a model expansion
40: to `blockStage ξ` (up to isomorphism; on the counted carrier by normalization). -/
41: def domain (ξ : Ordinal.{0}) : Set Classes :=
42:   {q | Quotient.lift
43:     (fun R : KnightNatModel => R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ))
44:     (fun _ _ h => propext (Realization.prolongsToIn_iff_of_iso
45:       (KnightNatModel.iso_atBlockZero (knightModelSetoid_r_iff.mp h)) _)) q}
46: 
47: theorem mem_domain_mk {ξ : Ordinal.{0}} (R : KnightNatModel) :
48:     Quotient.mk knightModelSetoid R ∈ domain ξ ↔
49:       R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ) :=
50:   Iff.rfl
51: 
52: /-- Membership normalizes to an actual model on the counted carrier. -/
53: theorem exists_model_of_mem_domain {ξ : Ordinal.{0}} {R : KnightNatModel}
54:     (h : Quotient.mk knightModelSetoid R ∈ domain ξ) :
55:     ∃ W : KnightRealization (blockStage ξ) ℕ,
56:       W.IsModel ∧ W.reduct (blockStage_zero_le ξ) = R.atBlockZero :=
57:   (prolongsToIn_isModelClass_iff_on _ _).mp h
58: 
59: theorem mem_domain_of_model {ξ : Ordinal.{0}} {R : KnightNatModel}
60:     {W : KnightRealization (blockStage ξ) ℕ} (hW : W.IsModel)
61:     (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
62:     Quotient.mk knightModelSetoid R ∈ domain ξ :=
63:   Realization.ProlongsToOnIn.prolongsToIn ⟨W, hW, hWr⟩
64: 
65: /-- Every class expands to block `0`. -/
66: theorem domain_zero : domain 0 = Set.univ := by
67:   ext q
68:   refine ⟨fun _ => trivial, fun _ => ?_⟩
69:   induction q using Quotient.inductionOn with
70:   | h R =>
71:     exact mem_domain_of_model (R := R) (R.2.reduct blockStage_zero_le_omegaStage)
72:       (Realization.reduct_refl _)
73: 
74: /-- **Expansion domains decrease**: an expansion to a higher block reduces to a lower one. -/
75: theorem domain_antitone : Antitone domain := by
76:   intro ξ η hξη q hq
77:   induction q using Quotient.inductionOn with
78:   | h R =>
79:     exact Realization.ProlongsToIn.mono isModelClass_reduct (blockStage_mono hξη) hq
80: 
81: /-! ## Successor losses -/
82: 
83: /-- A class lost at the next block is the class of a terminal model at this block. -/
84: theorem loss_subset_range (ξ : Ordinal.{0}) :
85:     domain ξ \ domain (ξ + 1) ⊆ Set.range (terminalToClass ξ) := by
86:   rintro q ⟨hq, hq'⟩
87:   induction q using Quotient.inductionOn with
88:   | h R =>
89:     obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
90:     have hterm : W.NoProlongationToIn IsModelClass (blockStage_le_succ ξ) := by
91:       intro hprol
92:       obtain ⟨V, hVm, hVr⟩ :=
93:         (prolongsToIn_isModelClass_iff_on W (blockStage_le_succ ξ)).mp hprol
94:       refine hq' (mem_domain_of_model hVm ?_)
95:       rw [← Realization.reduct_reduct (blockStage_zero_le ξ) (blockStage_le_succ ξ) V, hVr,
96:         hWr]
97:     refine ⟨Quotient.mk _ ⟨W, hWm, hterm⟩, ?_⟩
98:     change Quotient.mk knightModelSetoid (TerminalModel.toNatModel ⟨W, hWm, hterm⟩) =
99:       Quotient.mk knightModelSetoid R
100:     congr 1
101:     apply Subtype.ext
102:     change liftBlockZero (W.reduct (blockStage_zero_le ξ)) = R.1
103:     rw [hWr]
104:     exact liftBlockZero_reduct R.1
105: 
106: /-- **Successor losses are countable**, given countable terminal fibres. -/
107: theorem loss_countable (hct : CountableTerminalFibres) {ξ : Ordinal.{0}}
108:     (hξ : ξ < (aleph 1).ord) : (domain ξ \ domain (ξ + 1)).Countable :=
109:   have : Countable (TerminalClass ξ) := Cardinal.mk_le_aleph0_iff.mp (hct ξ hξ)
110:   (Set.countable_range _).mono (loss_subset_range ξ)
111: 
112: /-! ## Limits -/
113: 
114: /-- **No loss at a countable limit**: the countable-limit expansion theorem. -/
115: theorem iInter_subset_domain {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
116:     (hlω : l < (aleph 1).ord) : (⋂ ξ < l, domain ξ) ⊆ domain l := by
117:   intro q hq
118:   induction q using Quotient.inductionOn with
119:   | h R =>
120:     obtain ⟨W, hWm, hWr⟩ := exists_model_at_limit_of_forall_lt hl hlω (R := R.atBlockZero)
121:       fun ξ hξ => exists_model_of_mem_domain (Set.mem_iInter₂.mp hq ξ hξ)
122:     exact mem_domain_of_model hWm hWr
123: 
124: /-- **Full limit continuity**: at a countable limit the domain is the intersection of the
125: earlier domains (decreasingness gives one inclusion, limit expansion the other). -/
126: theorem domain_limit_eq {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
127:     (hlω : l < (aleph 1).ord) : domain l = ⋂ ξ < l, domain ξ :=
128:   Set.Subset.antisymm (Set.subset_iInter₂ fun _ hξ => domain_antitone hξ.le)
129:     (iInter_subset_domain hl hlω)
130: 
131: /-- **Fixed-stage complements are countable.** -/
132: theorem compl_countable (hct : CountableTerminalFibres) {β : Ordinal.{0}}
133:     (hβ : β < (aleph 1).ord) : (domain β)ᶜ.Countable :=
134:   CountableLoss.compl_countable_of_loss domain domain_zero
135:     (fun _ hξ => loss_countable hct hξ) (fun _ hl hlω => iInter_subset_domain hl hlω) β hβ
136: 
137: /-! ## Fixed-stage comparison on a domain -/
138: 
139: theorem reduct_omegaStage_eq {ξ : Ordinal.{0}} {R : KnightNatModel}
140:     {W : KnightRealization (blockStage ξ) ℕ}
141:     (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
142:     W.reduct (omegaStage_le _) = R.1 := by
143:   rw [← Realization.reduct_reduct omegaStage_le_blockStage_zero (blockStage_zero_le ξ) W, hWr]
144:   exact liftBlockZero_reduct R.1
145: 
146: /-- Classes in the domain at the comparison block agree on sentences of bounded rank. -/
147: theorem realizes_iff_of_mem_domain (hobr : OneBlockReadback.{0}) (φ : knightLang.Sentenceω)
148:     {η : Ordinal.{0}} (hφ : φ.qrank ≤ η) {q s : Classes}
149:     (hq : q ∈ domain (Ordinal.omega0 * η)) (hs : s ∈ domain (Ordinal.omega0 * η)) :
150:     realizes φ q ↔ realizes φ s := by
151:   revert hq hs
152:   refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
153:   obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
154:   obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hs
155:   have h := agree_sentence_of_obr hobr W V hWm hVm φ hφ
156:   rw [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h
157:   exact h
158: 
159: /-- The comparison block of a sentence is countable (as in `SentenceMinimality.threshold_lt`). -/
160: theorem threshold_lt (φ : knightLang.Sentenceω) :
161:     Ordinal.omega0 * φ.qrank < (aleph 1).ord := by
162:   rw [Cardinal.lt_ord, Ordinal.card_mul, Ordinal.card_omega0]
163:   exact (mul_le_mul' le_rfl
164:     (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (qrank_lt_ord_aleph_one φ)))).trans_lt
```

### `VaughtConjecture/Knight/ExpansionDomainUniform.lean` — lines 7–47

SHA-256: `e65b8fdfd97ce3b79abe0bf60e3dc62a0cb21d317de895892d048315dfdb973c`.

```text
7: import VaughtConjecture.Knight.UniformCoverComparisonCore
8: 
9: /-! # Homogeneous expansion domains at the sentence's own rank
10: 
11: Uniform finite-cover transfer removes the extra `ω`-factor from the expansion
12: domain's comparison budget. The old one-block interface is retained unchanged.
13: These statements use expansion existence directly, not stopping ranks, and
14: terminal countability is needed only to count the exceptional classes.
15: -/
16: 
17: namespace VaughtConjecture.Knight.ExpansionDomain
18: 
19: open TypeTower FirstOrder Language KnightRealization StoppingRankFiltration
20: 
21: /-- Membership in the expansion domain at `η` suffices for agreement on all
22: sentences of quantifier rank at most `η`. -/
23: theorem realizes_iff_of_mem_domain_uniform (φ : knightLang.Sentenceω)
24:     {η : Ordinal.{0}} (hφ : φ.qrank ≤ η) {q s : Classes}
25:     (hq : q ∈ domain η) (hs : s ∈ domain η) : realizes φ q ↔ realizes φ s := by
26:   revert hq hs
27:   refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
28:   obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
29:   obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hs
30:   have h := agree_sentence_uniform W V hWm hVm φ hφ
31:   rw [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h
32:   exact h
33: 
34: /-- Every sentence has a countable truth side; its own rank is the comparison
35: threshold. No eventual-departure hypothesis is needed. -/
36: theorem sentence_split_countable_uniform (hct : CountableTerminalFibres)
37:     (φ : knightLang.Sentenceω) :
38:     ({q : Classes | realizes φ q} : Set Classes).Countable ∨
39:       ({q : Classes | ¬ realizes φ q} : Set Classes).Countable := by
40:   have hc := compl_countable hct (qrank_lt_ord_aleph_one φ)
41:   by_cases h : ∃ q ∈ domain φ.qrank, realizes φ q
42:   · obtain ⟨q₀, hq₀, hr⟩ := h
43:     exact Or.inr (Set.Countable.mono (fun s hs hsd =>
44:       hs ((realizes_iff_of_mem_domain_uniform φ le_rfl hsd hq₀).mpr hr)) hc)
45:   · exact Or.inl (Set.Countable.mono (fun q hq hqd => h ⟨q, hqd, hq⟩) hc)
46: 
47: end VaughtConjecture.Knight.ExpansionDomain
```

## A9. Literal descriptive interface and standard upper bound

### `VaughtConjecture/Knight/ExpansionDomainThinnessCore.lean` — lines 7–40

SHA-256: `33926022f29b24623eddeac1d74203024bb772e0afd2c3c707e511effb91e37b`.

```text
7: import VaughtConjecture.Knight.ClassPresentation
8: import InfinitaryLogic.Descriptive.SmallVocabularyTransport
9: import VaughtConjecture.Spectrum.Thinness
10: 
11: /-! # Thinness from expansion domains, with the construction inputs explicit
12: 
13: Countable terminal fibres and one-block readback give countable sentence splits;
14: standard invariant sentence separation then gives thinness. The construction
15: producers live in the compatibility facade `ExpansionDomainThinness`.
16: 
17: The proof uses no stopping rank, termination theorem, canonical stopping
18: expansion or high-stage existence. This is a proof-dependency statement: the
19: existing terminal definitions still have wider imports.
20: -/
21: 
22: namespace VaughtConjecture.Knight.ExpansionDomain
23: 
24: open FirstOrder Language Spectrum Cardinal StoppingRankFiltration
25: 
26: /-- The class truth predicate is ordinary satisfaction on coded models
27: (`ClassPresentation.realizes_modelClass`; retained under this name). -/
28: theorem realizes_classOfCode (φ : knightLang.Sentenceω) (c : ModelsOf knightSentence) :
29:     realizes φ (classOfCode (Quotient.mk (isoSetoid knightSentence) c)) ↔
30:       c.1 ∈ ModelsOf φ :=
31:   realizes_modelClass φ c
32: 
33: /-- **Rank-free thinness**, with terminal countability and receiving explicit: the
34: library's thinness from single-sentence splits on the class presentation. -/
35: theorem isThinOnNatModels_of (hct : CountableTerminalFibres) (hobr : OneBlockReadback.{0}) :
36:     knightSentence.IsThinOnNatModels :=
37:   SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits knightLang knightSentence
38:     modelClass realizes realizes_modelClass (sentence_split_countable hct hobr)
39: 
40: end VaughtConjecture.Knight.ExpansionDomain
```

### `VaughtConjecture/Spectrum/Sentence.lean` — lines 7–112

SHA-256: `c26711569c4303cfb2e98040de6f02e965a1cda41f4a109ef02d9f7600412613`.

```text
7: import InfinitaryLogic.Conditional.GandyHarrington
8: import InfinitaryLogic.Conditional.MorleyPerfect
9: import VaughtConjecture.Spectrum.RankCount
10: 
11: /-! # The countable spectrum of an `L_{ω₁,ω}` sentence
12: 
13: We take the notion of "countable models up to isomorphism" from
14: `InfinitaryLogic`.  Two counts are kept apart:
15: 
16: * `natModelSpectrum φ := #(Quotient (isoSetoid φ))` — isomorphism classes of `ℕ`-models,
17:   i.e. models of cardinality exactly `ℵ₀`.  This is the standard `I(φ, ℵ₀)`.
18: * `allCountableSpectrum φ := #(AllCodedIsoClasses φ)` — all carrier tiers (`ℕ` and every
19:   `Fin n`), faithfully representing all countable models by `codeModel`,
20:   `codeModel_eq_of_iso`, `iso_of_codeModel_eq`, `codeModel_surjective`.
21: 
22: The two agree when `φ` has no finite models (`HasNoFiniteModels`,
23: `allCountableSpectrum_eq_natModelSpectrum`).  Conventional names
24: (`CardinalVaughtConjectureFor`, and `VaughtConjecturePerfectSetFor` in `Spectrum.Thinness`)
25: refer to the `ℕ`-tier forms; the all-tier variants carry the prefix `AllCountable`.
26: 
27: * Morley's theorem (`morley_counting_coded` / `morley_counting`, unconditional in
28:   `InfinitaryLogic` via its proof of the Silver–Burgess dichotomy) gives
29:   `I(φ,ℵ₀) ≤ ℵ₁ ∨ I(φ,ℵ₀) = 2^ℵ₀` in both forms.  The witnessed refinements
30:   (`morley_counting_coded_or_perfect` / `morley_counting_or_perfect`) put a perfect set of
31:   pairwise non-isomorphic models in the second alternative; their spectrum-named adapters are
32:   `natModelSpectrum_le_aleph_one_or_perfectSet` /
33:   `allCountableSpectrum_le_aleph_one_or_perfectSet`.
34: * `natModelSpectrum_eq_aleph_one_of_rank` / `allCountableSpectrum_eq_aleph_one_of_rank`: the
35:   shape of Knight's headline — a total rank into `ω₁` with countable fibres and cofinal range
36:   on the isomorphism classes forces exactly `ℵ₁` classes.
37: * `not_cardinalVaughtConjectureFor_of_eq_aleph_one`: under `¬CH`, `I(φ,ℵ₀) = ℵ₁` refutes the
38:   cardinal form.  The CH-independent (perfect-set) form needs the separate thinness statement;
39:   see `Spectrum.Thinness` and `docs/DESIGN.md`. -/
40: 
41: namespace VaughtConjecture.Spectrum
42: 
43: open FirstOrder Language Cardinal
44: 
45: universe u v w
46: 
47: variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
48: 
49: /-- The standard `I(φ, ℵ₀)`: isomorphism classes of `ℕ`-models of `φ` (models of cardinality
50: exactly `ℵ₀`). -/
51: noncomputable def natModelSpectrum (φ : L.Sentenceω) : Cardinal :=
52:   #(Quotient (isoSetoid φ))
53: 
54: /-- The all-countable variant: isomorphism classes of countable models of `φ` over **all**
55: carrier tiers (`ℕ`-models and every `Fin n` tier). -/
56: noncomputable def allCountableSpectrum (φ : L.Sentenceω) : Cardinal :=
57:   #(AllCodedIsoClasses φ)
58: 
59: /-- `φ` has no finite models (every `Fin n` tier of coded models is empty). -/
60: def HasNoFiniteModels (φ : L.Sentenceω) : Prop :=
61:   ∀ n : ℕ, ModelsOfOn (α := Fin n) φ = ∅
62: 
63: omit [Countable (Σ l, L.Relations l)] in
64: /-- Without finite models, the all-countable spectrum is the standard `I(φ, ℵ₀)`. -/
65: theorem allCountableSpectrum_eq_natModelSpectrum {φ : L.Sentenceω} (h : HasNoFiniteModels φ) :
66:     allCountableSpectrum φ = natModelSpectrum φ := by
67:   have hempty : IsEmpty (Σ n, Quotient (isoSetoidOn φ n)) := by
68:     refine ⟨fun ⟨n, q⟩ => ?_⟩
69:     induction q using Quotient.inductionOn with
70:     | h c => exact (Set.eq_empty_iff_forall_notMem.mp (h n)) c.1 c.2
71:   unfold allCountableSpectrum natModelSpectrum AllCodedIsoClasses
72:   rw [mk_sum, mk_eq_zero (Σ n, Quotient (isoSetoidOn φ n)), lift_zero, add_zero, lift_id]
73: 
74: /-- The **cardinal** form of Vaught's conjecture for `φ` (`ℕ`-tier): countably many or
75: continuum many countable models.  (The CH-independent perfect-set form is
76: `VaughtConjecturePerfectSetFor` in `Spectrum.Thinness`.) -/
77: def CardinalVaughtConjectureFor (φ : L.Sentenceω) : Prop :=
78:   natModelSpectrum φ ≤ ℵ₀ ∨ natModelSpectrum φ = continuum
79: 
80: /-- The all-countable variant of the cardinal form (all carrier tiers). -/
81: def AllCountableCardinalVaughtConjectureFor (φ : L.Sentenceω) : Prop :=
82:   allCountableSpectrum φ ≤ ℵ₀ ∨ allCountableSpectrum φ = continuum
83: 
84: /-- Morley's theorem, `ℕ`-tier: `I(φ, ℵ₀) ≤ ℵ₁` or `I(φ, ℵ₀) = 2^ℵ₀`. -/
85: theorem natModelSpectrum_le_aleph_one_or_eq_continuum (φ : L.Sentenceω) :
86:     natModelSpectrum φ ≤ aleph 1 ∨ natModelSpectrum φ = continuum :=
87:   morley_counting_coded silverBurgessDichotomy φ
88: 
89: /-- Morley's theorem, all-countable variant.  Proved from the witnessed dichotomy
90: (`morley_counting_or_perfect_cardinal`), so no `SilverBurgessDichotomy` argument is needed. -/
91: theorem allCountableSpectrum_le_aleph_one_or_eq_continuum (φ : L.Sentenceω) :
92:     allCountableSpectrum φ ≤ aleph 1 ∨ allCountableSpectrum φ = continuum :=
93:   morley_counting_or_perfect_cardinal φ
94: 
95: /-- Morley counting with a witness, `ℕ`-tier: at most `ℵ₁` isomorphism classes, or a perfect
96: set of pairwise non-isomorphic `ℕ`-models. -/
97: theorem natModelSpectrum_le_aleph_one_or_perfectSet (φ : L.Sentenceω) :
98:     natModelSpectrum φ ≤ aleph 1 ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels :=
99:   morley_counting_coded_or_perfect φ
100: 
101: /-- Morley counting with a witness, all-countable variant: at most `ℵ₁` classes over all
102: tiers, or a perfect set of pairwise non-isomorphic models in some carrier tier. -/
103: theorem allCountableSpectrum_le_aleph_one_or_perfectSet (φ : L.Sentenceω) :
104:     allCountableSpectrum φ ≤ aleph 1 ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
105:       ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n :=
106:   morley_counting_or_perfect φ
107: 
108: omit [Countable (Σ l, L.Relations l)] in
109: /-- The ranked-realization kernel on the isomorphism classes of `ℕ`-models: a total,
110: countable-fibred, cofinal rank into `ω₁` gives `I(φ, ℵ₀) = ℵ₁`. -/
111: theorem natModelSpectrum_eq_aleph_one_of_rank (φ : L.Sentenceω)
112:     (ρ : Quotient (isoSetoid φ) → Ordinal.{w})
```

### `VaughtConjecture/Knight/ExpansionDomainEndpoint.lean` — lines 27–64

SHA-256: `69213042836977697a7c1dcdf69dd2a2e3cb1cb07afd6c7d455c4558408e20af`.

```text
27: open FirstOrder Language Cardinal Spectrum StoppingRankFiltration
28: 
29: /-- Rank-free thinness, using the uniform finite-cover comparison budget: the library's
30: thinness from single-sentence splits on the class presentation. -/
31: theorem isThinOnNatModels : knightSentence.IsThinOnNatModels :=
32:   SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits knightLang knightSentence
33:     modelClass realizes realizes_modelClass
34:     (ExpansionDomain.sentence_split_countable_uniform
35:       ConstructedSpectrumEndpoint.countableTerminalFibres)
36: 
37: /-- The upper bound is the standard witnessed Morley dichotomy, not a count of
38: canonical stopping expansions. -/
39: theorem natModelSpectrum_le_aleph_one : natModelSpectrum knightSentence ≤ aleph 1 :=
40:   Spectrum.natModelSpectrum_le_aleph_one_of_thin isThinOnNatModels
41: 
42: /-- Exact spectrum from standard thinness counting and locally constructed losses. -/
43: theorem natModelSpectrum_eq_aleph_one : natModelSpectrum knightSentence = aleph 1 := by
44:   apply le_antisymm natModelSpectrum_le_aleph_one
45:   rw [natModelSpectrum_knightSentence]
46:   exact ExpansionDomain.aleph_one_le_classes
47: 
48: /-- The all-countable-carrier spectrum agrees, since there are no finite models. -/
49: theorem allCountableSpectrum_eq_aleph_one : allCountableSpectrum knightSentence = aleph 1 :=
50:   allCountableSpectrum_knightSentence.trans natModelSpectrum_eq_aleph_one
51: 
52: /-- The natural-number perfect-set property fails, independently of global termination. -/
53: theorem not_vaughtConjecturePerfectSetFor : ¬ VaughtConjecturePerfectSetFor knightSentence :=
54:   not_vaughtConjecturePerfectSetFor_of_thin
55:     (by rw [natModelSpectrum_eq_aleph_one]; exact aleph0_lt_aleph_one) isThinOnNatModels
56: 
57: /-- The all-countable perfect-set property fails, with the finite-tier guard explicit. -/
58: theorem not_allCountableVaughtConjecturePerfectSetFor :
59:     ¬ AllCountableVaughtConjecturePerfectSetFor knightSentence :=
60:   not_allCountableVaughtConjecturePerfectSetFor_of_thin
61:     (by rw [allCountableSpectrum_eq_aleph_one]; exact aleph0_lt_aleph_one)
62:     isThinOnNatModels hasNoFiniteModels_knightSentence
63: 
64: end VaughtConjecture.Knight.ExpansionDomainEndpoint
```

## A10. Independent top-free terminal losses and lower bound

### `VaughtConjecture/Knight/ConstructedTerminalLoss.lean` — lines 7–54

SHA-256: `5e17e3f198581a56dcaf0b0b875a87115a4968c0cd79cb1b2f436efc5d163a87`.

```text
7: import VaughtConjecture.Knight.TopFreeCapHenkin
8: 
9: /-! # Nonempty losses and the lower spectrum bound without global termination
10: 
11: The top-free capped scheduler constructs a terminal model at every countable
12: block. Unique expansion puts its base class in that block's successor loss.
13: These losses are disjoint, so choosing one class in each injects the countable
14: ordinals into the counted classes. No classification or global termination is
15: used to produce these witnesses or obtain the lower cardinal bound.
16: -/
17: 
18: namespace VaughtConjecture.Knight.ExpansionDomain
19: 
20: open TypeTower KnightRealization Cardinal StoppingRankFiltration
21: 
22: /-- Every countable block has a nonempty successor loss, supplied by a locally
23: constructed top-free terminal model. This includes block zero. -/
24: theorem loss_nonempty {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
25:     (domain ξ \ domain (ξ + 1)).Nonempty := by
26:   obtain ⟨W, hW, hterm⟩ := TopFreeCapHenkin.exists_terminal_model
27:     (β := blockStage ξ) (M := ℕ)
28:     (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hξ)))
29:   exact ⟨_, terminalModel_mem_loss ⟨W, hW,
30:     hterm _ (blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl))⟩⟩
31: 
32: /-- In particular successor losses are cofinally nonempty below `ω₁`. -/
33: theorem cofinal_losses (η : Ordinal.{0}) (hη : η < (aleph 1).ord) :
34:     ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧ (domain ξ \ domain (ξ + 1)).Nonempty :=
35:   ⟨η, le_rfl, hη, loss_nonempty hη⟩
36: 
37: /-- The lower bound comes from disjoint successor losses, not from a stopping
38: rank or a theorem asserting that every class eventually departs. -/
39: theorem aleph_one_le_classes : aleph 1 ≤ #Classes := by
40:   classical
41:   choose q hq using fun ξ : Set.Iio (aleph 1).ord => loss_nonempty ξ.2
42:   have hinj : Function.Injective q := by
43:     intro ξ η heq
44:     apply Subtype.ext
45:     apply le_antisymm
46:     · by_contra hle
47:       exact (hq η).2 (domain_antitone (Order.add_one_le_of_lt (lt_of_not_ge hle))
48:         (heq ▸ (hq ξ).1))
49:     · by_contra hle
50:       exact (hq ξ).2 (domain_antitone (Order.add_one_le_of_lt (lt_of_not_ge hle))
51:         (heq.symm ▸ (hq η).1))
52:   simpa only [CountableLoss.mk_Iio_ord_aleph_one] using Cardinal.mk_le_of_injective hinj
53: 
54: end VaughtConjecture.Knight.ExpansionDomain
```

### `VaughtConjecture/Knight/TopFreeCapHenkin.lean` — lines 7–110

SHA-256: `28758286a5fa59b3befe1507c529f757e6ab579a70791a7124f5f07872bdadac`.

```text
7: import VaughtConjecture.Knight.FiniteMasterState
8: import VaughtConjecture.Knight.FiniteRequestData
9: import VaughtConjecture.Knight.FixedHeightChain
10: import VaughtConjecture.Knight.CapReceivingModel
11: import VaughtConjecture.Knight.TopFreeTerminal
12: import VaughtConjecture.TypeTower.FiniteMasterScheduler
13: 
14: /-! # Capped scheduling with top-free masters
15: 
16: Requests specify a whole coface and an observation cutoff. The existence endpoint
17: uses the shared finite-master dense-set scheduler: absorb the root, then resolve
18: the request permanently. Each finite step uses the constructed top-free pinned
19: extension, and every union label comes from a top-free finite master.
20: 
21: The historical repeated-run statements remain for compatibility, but neither
22: existence endpoint uses them. Only the donor is approximated at a cutoff; the old
23: master is always retained literally. No exact realization of a top donor is claimed.
24: -/
25: 
26: namespace VaughtConjecture.Knight.TopFreeCapHenkin
27: open TypeTower StageType Value ExtOrd KnightRealization FixedHeight AmalgamationPlan
28: universe w
29: variable {β : LimitStage} {M : Type w}
30: 
31: structure State (β : LimitStage) (M : Type w) extends RunState β M where
32:   proper : ∀ d, P.label d ≠ ⊤
33: 
34: theorem State.topFree (st : State β M) {n : ℕ} (t : Fin n ↪ M)
35:     (p : S β.1 n) (hp : st.A.eval t = some p) : ∀ d, p.label d ≠ ⊤ := by
36:   obtain ⟨f, rfl⟩ := st.hM t (by rw [hp]; rfl)
37:   have hf : typeMap f st.P = some p := (st.hA.consistent _ _ f st.htup).symm.trans hp
38:   have hv := (typeMap_isSome_iff f st.P).mp (by rw [hf]; rfl)
39:   have he := Option.some.inj ((typeMap_eq_some f st.P hv).symm.trans hf)
40:   subst p
41:   exact fun d => st.proper _
42: 
43: noncomputable def initial (β : LimitStage) (M : Type w) : State β M :=
44:   { initState β M with
45:     proper := by
46:       intro d
47:       have hp := (initState β M).P.scheme.scheme.grade_pos d
48:       have h := FiniteCoverReceiving.grade_le_points (initState β M).P.scheme d
49:       change (initState β M).P.scheme.scheme.grade d ≤ 0 at h
50:       omega }
51: 
52: theorem install (st : State β M) {y : M} (hy : y ∉ Set.range st.tup)
53:     (Q : S β.1 (st.N + 1)) (hQ : IsCoface st.P Q) (hproper : ∀ d, Q.label d ≠ ⊤) :
54:     ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
55:       st'.A.eval (snoc st.tup y hy) = some Q ∧ y ∈ Set.range st'.tup := by
56:   let st' : State β M := ⟨RunState.ofMaster ⟨_, snoc st.tup y hy, Q⟩, hproper⟩
57:   have hm : st.toRunState.master ≤ st'.toRunState.master :=
58:     ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc st.tup y hy, hQ⟩
59:   exact ⟨st', RunState.extends_of_master hm, hm.range_mono, st'.htup,
60:     ⟨Fin.last _, snoc_apply_last st.tup y hy⟩⟩
61: 
62: abbrev Request (β : LimitStage) (M : Type w) :=
63:   Σ n, (Fin n ↪ M) × Σ p : S β.1 n,
64:     {q : S β.1 (n + 1) // IsCoface p q} × {ν : Ordinal.{0} // ν < β.1}
65: 
66: def Applicable (A : KnightRealization β M) : Request β M → Prop
67:   | ⟨_, t, p, _, _⟩ => A.eval t = some p
68: 
69: def Serves (A : KnightRealization β M) : Request β M → Prop
70:   | ⟨n, t, _, q, ν⟩ =>
71:     ∃ (y : M) (hy : y ∉ Set.range t) (r : S β.1 (n + 1)),
72:       A.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.1.scheme,
73:         ∀ d, min (r.label d) (ofOrd ν.1) =
74:           min (q.1.label (SemScheme.castCell he d)) (ofOrd ν.1)
75: 
76: theorem service [Infinite M] (st : State β M) (r : Request β M)
77:     (hr : Applicable st.A r) :
78:     ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
79:       Serves st'.A r := by
80:   obtain ⟨n, t, p, q, ν⟩ := r
81:   obtain ⟨f, hf⟩ := st.hM t (by rw [show st.A.eval t = some p from hr]; rfl)
82:   have hface : typeMap f st.P = some p := by
83:     have hh := st.hA.consistent _ _ f st.htup
84:     rw [hf] at hh
85:     exact hh.symm.trans hr
86:   obtain ⟨Q, hQP, hQtop, q', hQq, he, hcap⟩ := TopFreePinnedExtension.exists_pinned
87:     st.P st.proper f p hface q.1 q.2 (ofOrd ν.1) (ofOrd_lt_ofOrd.mpr ν.2)
88:   obtain ⟨y, hy, _⟩ := exists_fresh st.hA.finite st.tup
89:   obtain ⟨st', hext, hrange, hQ, _⟩ := install st hy Q hQP hQtop
90:   have hyt : y ∉ Set.range t := by
91:     rintro ⟨i, rfl⟩
92:     exact hy ⟨f i, congrArg (fun e : Fin n ↪ M => e i) hf⟩
93:   refine ⟨st', hext, hrange, y, hyt, q', ?_, he, hcap⟩
94:   have htup : (extendFace f).trans (snoc st.tup y hy) = snoc t y hyt := by
95:     subst t
96:     exact extendFace_trans_snoc f hy hyt
97:   rw [← htup]
98:   rw [st'.hA.consistent _ Q (extendFace f) hQ]
99:   exact hQq
100: 
101: theorem absorb (st : State β M) {x : M} (hx : x ∉ Set.range st.tup) :
102:     ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
103:       x ∈ Set.range st'.tup := by
104:   obtain ⟨q, _, hq⟩ := exists_highGrade_coface (CanonicalCoatomSupply.supply β.2)
105:     st.P 0 β.2.pos
106:   obtain ⟨Q, hQ, hproper, _⟩ := TopFreePinnedExtension.exists_pinned st.P st.proper
107:     (Function.Embedding.refl _) st.P (typeMap_refl _) q hq ⊥ (bot_lt_ofOrd _)
108:   obtain ⟨st', hext, hrange, _, hx'⟩ := install st hx Q hQ hproper
109:   exact ⟨st', hext, hrange, hx'⟩
110: 
```

## A11. Global hull already implemented

### `VaughtConjecture/Knight/GlobalHull.lean` — lines 7–131

SHA-256: `a7250a425da9fe4f71dc369e726d489c607e95c44748467b28dbe8d15bca2654`.

```text
7: import VaughtConjecture.Knight.FiniteHull
8: import VaughtConjecture.AmalgamationPlan.AntiExchange
9: 
10: /-! # Finitary anti-exchange geometry of actual chart supports
11: 
12: Exact consistency and covering suffice: no modelhood, receiving, stability or
13: countability hypothesis is used. The canonical finite hull extends to all
14: subsets, with finite character, closed empty and singleton sets, and global
15: anti-exchange. Every individual membership has a witness of size at most two;
16: this is not two-generation of every infinite closed set.
17: 
18: The actual-hull API and all existing clients remain unchanged. Preservation
19: under isomorphisms/reducts and definability of coordinates are separate results.
20: -/
21: 
22: set_option autoImplicit false
23: 
24: namespace VaughtConjecture.Knight.KnightRealization.FiniteHull
25: 
26: open TypeTower StageType
27: 
28: variable {α : LimitStage} {M : Type*} [DecidableEq M]
29: variable {R : KnightRealization α M}
30: 
31: /-- Finite anti-exchange for actual supports, computed inside one containing chart. -/
32: theorem hull_antiExchange (hcons : R.IsExactParentConsistent)
33:     (hcov : R.IsInitialSegmentCovering) (S : Finset M) (a b : M)
34:     (hab : a ≠ b) (haS : a ∉ hull hcons hcov S)
35:     (ha : a ∈ hull hcons hcov (insert b S)) :
36:     b ∉ hull hcons hcov (insert a S) := by
37:   intro hb
38:   let H := hull hcons hcov S
39:   obtain ⟨_, ⟨z, rfl⟩, hz⟩ := exists_actual_superset hcov (insert a (insert b H))
40:   have hHz : H ⊆ support z.tuple :=
41:     (Finset.subset_insert _ _).trans ((Finset.subset_insert _ _).trans hz)
42:   obtain ⟨i, rfl⟩ := (mem_support z.tuple a).mp (hz (Finset.mem_insert_self _ _))
43:   obtain ⟨j, rfl⟩ := (mem_support z.tuple b).mp
44:     (hz (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
45:   let B := coordinates z H
46:   have he : B.image z.tuple = H := image_coordinates z H hHz
47:   have hB : B ∈ z.type.scheme.scheme.plan :=
48:     (actual_image_iff_face hcons z B).mp (he.symm ▸ hull_actual hcons hcov S)
49:   have hxi : i ∈ AmalgamationPlan.Plan.hull Finset.univ z.type.scheme.scheme.plan
50:       (insert j B) := by
51:     have hh := (hull hcons hcov).monotone
52:       (Finset.insert_subset_insert _ (subset_hull hcons hcov S)) ha
53:     change z.tuple i ∈ hull hcons hcov (insert (z.tuple j) H) at hh
54:     rw [← he, ← Finset.image_insert, hull_image hcons hcov z] at hh
55:     obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hh
56:     exact z.tuple.injective hki ▸ hk
57:   have hyj : j ∈ AmalgamationPlan.Plan.hull Finset.univ z.type.scheme.scheme.plan
58:       (insert i B) := by
59:     have hh := (hull hcons hcov).monotone
60:       (Finset.insert_subset_insert _ (subset_hull hcons hcov S)) hb
61:     change z.tuple j ∈ hull hcons hcov (insert (z.tuple i) H) at hh
62:     rw [← he, ← Finset.image_insert, hull_image hcons hcov z] at hh
63:     obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hh
64:     exact z.tuple.injective hkj ▸ hk
65:   exact z.type.scheme.scheme.isPlan.convexGeometry.anti_exchange hB
66:     (Finset.mem_univ i) (Finset.mem_univ j)
67:     (fun hij => hab (congrArg z.tuple hij))
68:     (fun hi => haS ((mem_coordinates z H i).mp hi)) hxi hyj
69: 
70: /-- The finitary closure on the whole carrier, extending canonical actual finite hulls. -/
71: noncomputable def closure (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) :
72:     ClosureOperator (Set M) := FiniteSupportClosure.setClosure (hull hcons hcov)
73: 
74: /-- On finite sets this is exactly the previously constructed actual hull. -/
75: theorem closure_finset (hcons : R.IsExactParentConsistent)
76:     (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
77:     closure hcons hcov (↑S : Set M) = (↑(hull hcons hcov S) : Set M) :=
78:   FiniteSupportClosure.setClosure_finset _ _
79: 
80: /-- Every global hull membership has a finite witness. -/
81: theorem mem_closure_iff (hcons : R.IsExactParentConsistent)
82:     (hcov : R.IsInitialSegmentCovering) {A : Set M} {a : M} :
83:     a ∈ closure hcons hcov A ↔
84:       ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ a ∈ hull hcons hcov S := Iff.rfl
85: 
86: /-- Each forced point has at most two generators in the input. This does not claim a
87: single pair generates the closure of an arbitrary infinite set. -/
88: theorem mem_closure_iff_pair (hcons : R.IsExactParentConsistent)
89:     (hcov : R.IsInitialSegmentCovering) {A : Set M} {a : M} :
90:     a ∈ closure hcons hcov A ↔
91:       ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ S.card ≤ 2 ∧ a ∈ hull hcons hcov S := by
92:   constructor
93:   · rintro ⟨S, hS, ha⟩
94:     obtain ⟨T, hTS, hT, he⟩ := exists_small_generator hcons hcov S
95:     exact ⟨T, fun x hx => hS (hTS hx), hT, he.symm ▸ ha⟩
96:   · rintro ⟨S, hS, _, ha⟩
97:     exact ⟨S, hS, ha⟩
98: 
99: /-- The empty set is closed. -/
100: @[simp] theorem closure_empty (hcons : R.IsExactParentConsistent)
101:     (hcov : R.IsInitialSegmentCovering) : closure hcons hcov ∅ = ∅ :=
102:   FiniteSupportClosure.setClosure_empty _ (hull_empty hcons hcov)
103: 
104: /-- Singletons are closed. -/
105: @[simp] theorem closure_singleton (hcons : R.IsExactParentConsistent)
106:     (hcov : R.IsInitialSegmentCovering) (a : M) : closure hcons hcov {a} = {a} := by
107:   simpa only [Finset.coe_singleton, hull_singleton] using closure_finset hcons hcov {a}
108: 
109: /-- The finite closed sets are precisely the actual chart supports. -/
110: theorem closure_finset_eq_iff_actual (hcons : R.IsExactParentConsistent)
111:     (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
112:     closure hcons hcov (↑S : Set M) = (↑S : Set M) ↔ IsActualSupport R S := by
113:   rw [closure_finset, Finset.coe_inj, hull_eq_iff_actual]
114: 
115: /-- Tuple evaluation is exactly closedness of its finite support. -/
116: theorem eval_isSome_iff_closure_eq (hcons : R.IsExactParentConsistent)
117:     (hcov : R.IsInitialSegmentCovering) {n : ℕ} (t : Fin n ↪ M) :
118:     (R.eval t).isSome ↔
119:       closure hcons hcov (↑(support t) : Set M) = (↑(support t) : Set M) :=
120:   (eval_isSome_iff_actual hcons t).trans (closure_finset_eq_iff_actual hcons hcov _).symm
121: 
122: /-- Global anti-exchange, using only exact consistency and covering. -/
123: theorem closure_antiExchange (hcons : R.IsExactParentConsistent)
124:     (hcov : R.IsInitialSegmentCovering) {A : Set M}
125:     (hA : closure hcons hcov A = A) {a b : M} (hab : a ≠ b) (haA : a ∉ A)
126:     (ha : a ∈ closure hcons hcov (insert b A)) :
127:     b ∉ closure hcons hcov (insert a A) :=
128:   FiniteSupportClosure.setClosure_antiExchange _ (hull_antiExchange hcons hcov)
129:     hA hab haA ha
130: 
131: end VaughtConjecture.Knight.KnightRealization.FiniteHull
```

### `VaughtConjecture/Order/FinitaryClosure.lean` — lines 7–70

SHA-256: `db49cde5e5f341ae0139f62610e2a5a0f9395f71bf061030ecd99e38da8a9288`.

```text
7: import Mathlib.Data.Finset.Union
8: 
9: /-! # From finite hulls to a finitary closure operator
10: 
11: This construction uses no model theory. The closure of a set is the union of
12: the hulls of its finite subsets. A common finite witness proves idempotence;
13: two such witnesses transfer anti-exchange from the finite operator.
14: -/
15: 
16: set_option autoImplicit false
17: 
18: namespace VaughtConjecture.FiniteSupportClosure
19: 
20: variable {M : Type*}
21: 
22: /-- Finite-character extension: a point is forced by a finite subset of the input. -/
23: def extension (c : ClosureOperator (Finset M)) (A : Set M) : Set M :=
24:   {x | ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ x ∈ c S}
25: 
26: /-- Monotonicity passes from finite hulls to arbitrary inputs. -/
27: theorem extension_mono (c : ClosureOperator (Finset M)) : Monotone (extension c) := by
28:   intro A B h x hx
29:   obtain ⟨S, hS, hx⟩ := hx
30:   exact ⟨S, hS.trans h, hx⟩
31: 
32: /-- Singleton witnesses make the extension extensive. -/
33: theorem subset_extension (c : ClosureOperator (Finset M)) (A : Set M) : A ⊆ extension c A := by
34:   intro x hx
35:   refine ⟨{x}, ?_, c.le_closure _ (Finset.mem_singleton_self x)⟩
36:   simpa using hx
37: 
38: /-- The extension agrees literally with the given operator on every finite input. -/
39: theorem extension_finset (c : ClosureOperator (Finset M)) (S : Finset M) :
40:     extension c (↑S : Set M) = (↑(c S) : Set M) := by
41:   ext x
42:   constructor
43:   · rintro ⟨T, hT, hx⟩
44:     exact c.monotone hT hx
45:   · intro hx
46:     exact ⟨S, Set.Subset.rfl, hx⟩
47: 
48: /-- Finitely many forced points have one common finite set of witnesses. -/
49: theorem finite_support (c : ClosureOperator (Finset M)) {A : Set M} (S : Finset M)
50:     (hS : (↑S : Set M) ⊆ extension c A) :
51:     ∃ T : Finset M, (↑T : Set M) ⊆ A ∧ S ⊆ c T := by
52:   classical
53:   induction S using Finset.induction_on with
54:   | empty => exact ⟨∅, by simp, Finset.empty_subset _⟩
55:   | @insert x S hx ih =>
56:     obtain ⟨U, hU, hxU⟩ := hS (Finset.mem_insert_self x S)
57:     obtain ⟨T, hT, hST⟩ := ih (fun y hy => hS (Finset.mem_insert_of_mem hy))
58:     refine ⟨U ∪ T, ?_, Finset.insert_subset ?_ ?_⟩
59:     · intro y hy
60:       rcases Finset.mem_union.mp hy with hy | hy
61:       · exact hU hy
62:       · exact hT hy
63:     · exact c.monotone Finset.subset_union_left hxU
64:     · exact hST.trans (c.monotone Finset.subset_union_right)
65: 
66: /-- Finite witnesses can be flattened, so closing twice adds nothing. -/
67: theorem extension_idem_le (c : ClosureOperator (Finset M)) (A : Set M) :
68:     extension c (extension c A) ⊆ extension c A := by
69:   rintro x ⟨S, hS, hx⟩
70:   obtain ⟨T, hT, hST⟩ := finite_support c S hS
```

## A12. Finite preservation and explicit first-order coordinate formulas already implemented

### `VaughtConjecture/Knight/FiniteHullPreservation.lean` — lines 7–100

SHA-256: `cb163758b8d881ae9814857b725bdf176e307c35e2fb0482e4d9f8a993104c79`.

```text
7: import VaughtConjecture.Knight.StableLiftCore
8: 
9: /-!
10: # Preservation of canonical finite hulls
11: 
12: The actual hull of `Knight/FiniteHull` depends only on *which* injective tuples are
13: evaluated, never on their labels.  Consequently:
14: 
15: * literal reduction (`Option.map` on evaluations) has the same actual supports and the same
16:   hull as its source (`actual_reduct_iff`, `hull_reduct`);
17: * the structural stable lift `stableLiftOf` has the same actual supports and the same hull as
18:   its source (`actual_stableLiftOf_iff`, `hull_stableLiftOf`);
19: * realization isomorphisms carry actual supports and hulls to actual supports and hulls
20:   (`actual_image_iff`, `image_hull`), by the least-hull property;
21: * two literal expansions of one source on the same carrier have the same hull, and the stable
22:   lift of a reduct has the hull of the original realization (`hull_eq_of_reduct_eq`,
23:   `hull_stableLiftOf_reduct`).
24: 
25: So a canonical expansion changes labels on a fixed finite closure geometry.  The consistency
26: and covering hypotheses are stated for one side only; the other side's are derived from the
27: existing preservation theorems (`IsExactParentConsistent.reduct`, `stableLiftOf_consistent`,
28: `IsIso.isExactParentConsistent`, and the covering analogues).
29: 
30: This is preservation of the closure operator on **finite** subsets of the carrier.  No
31: arbitrary-subset closure, carrier-wide anti-exchange, finite-master extension, or identification
32: with algebraic or definable closure is stated.
33: -/
34: 
35: namespace VaughtConjecture.Knight.KnightRealization.FiniteHull
36: 
37: open TypeTower
38: 
39: variable {M : Type*} [DecidableEq M]
40: 
41: noncomputable section
42: 
43: /-! ### Supports depend only on the domain of evaluation -/
44: 
45: section Domain
46: 
47: variable {α β : LimitStage} {R : KnightRealization α M} {R' : KnightRealization β M}
48: 
49: /-- Actual supports depend only on which tuples are evaluated.  No consistency or covering is
50: needed. -/
51: theorem actual_iff_of_isSome_iff
52:     (h : ∀ {n : ℕ} (t : Fin n ↪ M), (R.eval t).isSome ↔ (R'.eval t).isSome)
53:     (S : Finset M) : IsActualSupport R S ↔ IsActualSupport R' S := by
54:   constructor
55:   · rintro ⟨x, rfl⟩
56:     obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ((h x.tuple).mp (by rw [x.eval_eq]; rfl))
57:     exact ⟨⟨_, x.tuple, q, hq⟩, rfl⟩
58:   · rintro ⟨x, rfl⟩
59:     obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ((h x.tuple).mpr (by rw [x.eval_eq]; rfl))
60:     exact ⟨⟨_, x.tuple, q, hq⟩, rfl⟩
61: 
62: /-- Two realizations with the same actual supports have literally the same hull, by the
63: least-hull property on each side. -/
64: theorem hull_eq_of_actual_iff (hcons : R.IsExactParentConsistent)
65:     (hcov : R.IsInitialSegmentCovering) (hcons' : R'.IsExactParentConsistent)
66:     (hcov' : R'.IsInitialSegmentCovering)
67:     (h : ∀ S, IsActualSupport R S ↔ IsActualSupport R' S) :
68:     hull hcons hcov = hull hcons' hcov' := by
69:   refine ClosureOperator.ext _ _ fun S => Finset.Subset.antisymm ?_ ?_
70:   · exact hull_min hcons hcov ((h _).mpr (hull_actual hcons' hcov' S))
71:       (subset_hull hcons' hcov' S)
72:   · exact hull_min hcons' hcov' ((h _).mp (hull_actual hcons hcov S))
73:       (subset_hull hcons hcov S)
74: 
75: end Domain
76: 
77: /-! ### Literal reduction -/
78: 
79: section Reduct
80: 
81: variable {α β : LimitStage} {W : KnightRealization β M}
82: 
83: /-- Reduction maps `some` to `some` and `none` to `none`, so it has the same actual supports. -/
84: theorem actual_reduct_iff (h : α ≤ β) (S : Finset M) :
85:     IsActualSupport (W.reduct h) S ↔ IsActualSupport W S :=
86:   actual_iff_of_isSome_iff (fun t => by rw [Realization.reduct_eval, Option.isSome_map]) S
87: 
88: /-- **Reduction preserves the hull.**  The reduct's hypotheses are derived from those of the
89: higher-stage realization. -/
90: theorem hull_reduct (h : α ≤ β) (hcons : W.IsExactParentConsistent)
91:     (hcov : W.IsInitialSegmentCovering) :
92:     hull (hcons.reduct h) (hcov.reduct h) = hull hcons hcov :=
93:   hull_eq_of_actual_iff _ _ _ _ (actual_reduct_iff h)
94: 
95: /-- Two literal expansions of one source, on the same carrier, have the same actual supports.
96: No consistency or covering is needed. -/
97: theorem actual_iff_of_reduct_eq {γ : LimitStage} {W' : KnightRealization γ M}
98:     (h : α ≤ β) (h' : α ≤ γ) (hred : W.reduct h = W'.reduct h') (S : Finset M) :
99:     IsActualSupport W S ↔ IsActualSupport W' S := by
100:   rw [← actual_reduct_iff h, hred, actual_reduct_iff h']
```

### `VaughtConjecture/Knight/HullCoordinateFormulas.lean` — lines 7–88

SHA-256: `71fa40512c1e90186ec6ed0f32f111d2f451191b95afd9279ce17f43c03ad86a`.

```text
7: import VaughtConjecture.Knight.ChartLanguage
8: 
9: /-!
10: # Explicit formulas for hull coordinates
11: 
12: For a stage type `q` of arity `m`, coordinates `i₀ i₁` containing the extreme coordinates of
13: `q`'s plan, and a target coordinate `j`, the first-order formula of the stage chart language
14: `stageLang α`
15: 
16: `φ(x₀, x₁, y) := ∃ z̄, P_q(z̄) ∧ z_{i₀} = x₀ ∧ z_{i₁} = x₁ ∧ z_j = y`
17: 
18: (`hullCoordinateFormula`) has, in the chart structure of every exactly consistent covering
19: realization, exactly one solution `y` whenever `x₀, x₁` are the `i₀, i₁` coordinates of an
20: actual chart of type `q` (`existsUnique_hullCoordinateFormula`).  Existence is that chart;
21: uniqueness is the two-charts theorem `FiniteHull.eq_of_endpoints`, proved from the actual
22: hull geometry, not from automorphism rigidity.
23: 
24: So every coordinate of an actual chart is defined from its endpoint coordinates by an explicit
25: formula of the chart language, uniformly over consistent covering realizations.  The formula is
26: finitary and depends on `q`, `i₀`, `i₁`, `j`.  Nothing is claimed about the definable closure
27: of arbitrary sets, about algebraic closure, or about endpoints that are not the prescribed
28: coordinates of an actual chart of type `q`.
29: -/
30: 
31: namespace VaughtConjecture.Knight
32: 
33: open FirstOrder Language Structure TypeTower AmalgamationPlan.Plan
34: 
35: universe w
36: 
37: /-- `φ(x₀, x₁, y) := ∃ z̄, P_q(z̄) ∧ z_{i₀} = x₀ ∧ z_{i₁} = x₁ ∧ z_j = y`, a first-order formula
38: of the stage chart language with free variables `x₀, x₁, y` indexed by `Fin 3`. -/
39: def hullCoordinateFormula {α : LimitStage} {m : ℕ} (q : S α.1 m) (i₀ i₁ j : Fin m) :
40:     (stageLang α).Formula (Fin 3) :=
41:   BoundedFormula.exs (n := m)
42:     ((Relations.boundedFormula (L := stageLang α) (show (stageLang α).Relations m from q)
43:         fun k => Term.var (Sum.inr k)) ⊓
44:       (Term.var (Sum.inr i₀)).bdEqual (Term.var (Sum.inl 0)) ⊓
45:       (Term.var (Sum.inr i₁)).bdEqual (Term.var (Sum.inl 1)) ⊓
46:       (Term.var (Sum.inr j)).bdEqual (Term.var (Sum.inl 2)))
47: 
48: variable {α : LimitStage} {M : Type w}
49: 
50: /-- The meaning of `hullCoordinateFormula` in the chart structure of a realization. -/
51: theorem realize_hullCoordinateFormula (R : KnightRealization α M) {m : ℕ} (q : S α.1 m)
52:     (i₀ i₁ j : Fin m) (v : Fin 3 → M) :
53:     @Formula.Realize (stageLang α) M (stageStructureOf R) _
54:         (hullCoordinateFormula q i₀ i₁ j) v ↔
55:       ∃ z : Fin m ↪ M, R.eval z = some q ∧ z i₀ = v 0 ∧ z i₁ = v 1 ∧ z j = v 2 := by
56:   let _ := stageStructureOf R
57:   simp only [hullCoordinateFormula, BoundedFormula.realize_exs, BoundedFormula.realize_inf,
58:     BoundedFormula.realize_bdEqual, Term.realize_var,
59:     Sum.elim_inr, Sum.elim_inl]
60:   constructor
61:   · rintro ⟨xs, ⟨⟨⟨hi, hq⟩, h₀⟩, h₁⟩, h₂⟩
62:     exact ⟨⟨xs, hi⟩, hq, h₀, h₁, h₂⟩
63:   · rintro ⟨z, hz, h₀, h₁, h₂⟩
64:     exact ⟨z, ⟨⟨⟨z.injective, hz⟩, h₀⟩, h₁⟩, h₂⟩
65: 
66: /-- **Unique realization.**  In an exactly consistent covering realization, if `i₀, i₁` contain
67: the extreme coordinates of `q`'s plan, then for the endpoint coordinates of any actual chart `z`
68: of type `q`, the formula `hullCoordinateFormula q i₀ i₁ j` has exactly one solution, `z j`. -/
69: theorem existsUnique_hullCoordinateFormula {R : KnightRealization α M}
70:     (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) {m : ℕ}
71:     {q : S α.1 m} {i₀ i₁ : Fin m}
72:     (hends : extremes q.scheme.scheme.plan Finset.univ ⊆ {i₀, i₁}) (j : Fin m)
73:     {z : Fin m ↪ M} (hz : R.eval z = some q) :
74:     ∃! b : M, @Formula.Realize (stageLang α) M (stageStructureOf R) _
75:       (hullCoordinateFormula q i₀ i₁ j) ![z i₀, z i₁, b] := by
76:   refine ⟨z j, (realize_hullCoordinateFormula R q i₀ i₁ j _).mpr ⟨z, hz, rfl, rfl, rfl⟩, ?_⟩
77:   intro b hb
78:   obtain ⟨z', hz', h₀, h₁, h₂⟩ := (realize_hullCoordinateFormula R q i₀ i₁ j _).mp hb
79:   have hzz : z = z' := KnightRealization.FiniteHull.eq_of_endpoints hcons hcov hz hz'
80:     fun i hi => by
81:       rcases Finset.mem_insert.mp (hends hi) with rfl | hi'
82:       · exact h₀.symm
83:       · rw [Finset.mem_singleton.mp hi']
84:         exact h₁.symm
85:   rw [hzz]
86:   exact h₂.symm
87: 
88: end VaughtConjecture.Knight
```

## A13. Alternative ending already implemented, not a new proposal

### `VaughtConjecture/Knight/ConstructedDomainSeparation.lean` — lines 7–55

SHA-256: `cb88ec7c98d15a2fd7310dbde4ba72e7560617441701258c87433c8a9bf7e1a1`.

```text
7: import VaughtConjecture.Knight.ConstructedTerminalLoss
8: import VaughtConjecture.Knight.ConstructedTerminalCountability
9: import VaughtConjecture.Knight.OrdinaryOneBlockReceiving
10: 
11: /-! # Independent domain counting and eventual departure
12: 
13: The local top-free scheduler discharges the cofinal-loss input to Scott separation.
14: This gives two separate applications: a direct cardinality argument using only a
15: countable persistent core, and the stronger fact that every class eventually
16: leaves the expansion domains. The latter is not used by either cardinality proof.
17: 
18: The default-independent thinness/Morley endpoint in `ExpansionDomainEndpoint`
19: does not import this module. The old intrinsic termination and canonical-stop
20: theorems remain unchanged; this module constructs no canonical stopping rank.
21: -/
22: 
23: namespace VaughtConjecture.Knight.ConstructedDomainSeparation
24: 
25: open Cardinal StoppingRankFiltration
26: 
27: /-- Local terminal models supply the cofinal losses required by the generic API. -/
28: theorem cofinalLosses : ExpansionDomain.CofinalLosses :=
29:   ExpansionDomain.cofinal_losses
30: 
31: /-- Every class eventually leaves the domains, by Scott isolation and local losses,
32: not by intrinsic termination or canonical stopping. -/
33: theorem eventual_departure (q : Classes) :
34:     ∃ ξ, ξ < (aleph 1).ord ∧ q ∉ ExpansionDomain.domain ξ :=
35:   ExpansionDomain.exists_notMem_domain_of_cofinalLosses
36:     OrdinaryModelReceiving.oneBlockReadback cofinalLosses q
37: 
38: /-- There is no class admitting expansions to every countable block. -/
39: theorem persistent_core_eq_empty :
40:     (⋂ ξ < (aleph 1).ord, ExpansionDomain.domain ξ) = ∅ := by
41:   apply Set.eq_empty_of_forall_notMem
42:   intro q hq
43:   obtain ⟨ξ, hξ, hnot⟩ := eventual_departure q
44:   exact hnot (Set.mem_iInter₂.mp hq ξ hξ)
45: 
46: /-- An independent spectrum calculation: countable complements and the countable
47: Scott-separated core, with local losses for the lower bound. No Morley dichotomy
48: and no departure theorem are needed. -/
49: theorem natModelSpectrum_eq_aleph_one :
50:     Spectrum.natModelSpectrum knightSentence = aleph 1 :=
51:   ExpansionDomain.natModelSpectrum_eq_aleph_one_of_cofinalLosses
52:     ConstructedSpectrumEndpoint.countableTerminalFibres
53:     OrdinaryModelReceiving.oneBlockReadback cofinalLosses
54: 
55: end VaughtConjecture.Knight.ConstructedDomainSeparation
```

### `docs/guide/minimal-proof-route.md` — lines 88–111

SHA-256: `8b56a34a63fa67903b0de610e737f27a6bc08025740a7cc8fdbd6c944dc45567`.

```text
88: provides the isomorphism-compatible surjection from model codes. IL supplies
89: sentence-split thinness, Scott isolation/countable disjunctions, and countable
90: exception sets for Borel observations. Observable measurability is imposed on
91: the composite on model codes; the quotient itself has no measurable structure.
92: The exact spectrum still combines the standard thinness upper bound with the
93: independent construction of terminal losses.
94: 
95: Finite geometry, finite suppliers and finite installation now have separate
96: modules below scheduling (see the [finite-construction map](../notes/finite-construction-core.md)).
97: The top-free path excludes the historical Henkin/census modules; it still uses
98: the generic scheduler and chain union. Splitting these modules increases the
99: file count but makes the finite-versus-infinite proof boundary explicit.
100: 
101: The same one-block comparison also feeds the optional pointed Scott/formula
102: API in `PointedScott`. That consumer and the stopping-rank applications are not
103: imports of the recommended endpoint. Their former `ω * η` budget statements
104: remain compatibility corollaries, not a second comparison argument.
105: 
106: ## Three conclusions, not one overloaded proof
107: 
108: | Export | Mathematical role | Additional route used |
109: | --- | --- | --- |
110: | `ExpansionDomainEndpoint` | Recommended exact spectrum and perfect-set failures | Sentence separation and Morley; no global departure |
111: | `ConstructedDomainSeparation.natModelSpectrum_eq_aleph_one` | Alternative direct counting | Countable persistent core and cofinal losses; no Morley or departure |
```

## A14. Remaining compatibility imports and reproducibility pins

### `VaughtConjecture/Knight/GrowthProlongationBoundary.lean` — lines 7–47

SHA-256: `7b663976d719b95fa7889c19adc6fcc13ae33a7f4a3efaf6bc8cafe8905b8cda`.

```text
7: import VaughtConjecture.Knight.TopGradeStableSpectrum
8: 
9: /-! # Lemma 5.5.1 in growth/anchor vocabulary
10: 
11: The only positive half of Lemma 5.5.1, recast with the concrete top-grade growth predicate:
12: `ProlongationOrDefectAt W ↔ GrowthAnchorProlongationAt W` for models, so the
13: characteristic-arity quantifier disappears from the producer API.  Reviewer probe
14: (2026-09-04), graduated.  Construction-private (not root-exported). -/
15: 
16: namespace VaughtConjecture.Knight
17: 
18: open TypeTower KnightRealization
19: 
20: universe w
21: 
22: /-- Lemma 5.5.1 in the paper's operational vocabulary: an infinity anchor
23: (non-hollowness) plus unbounded top grade produces the next-block expansion. -/
24: def GrowthAnchorProlongationAt {M : Type w} {rho : Ordinal.{0}}
25:     (W : KnightRealization (blockStage rho) M) : Prop :=
26:   (¬ W.IsHollow ∧ W.HasTopGradeGrowth) →
27:     W.ProlongsToIn IsModelClass (blockStage_le_succ rho)
28: 
29: /-- For models, the existing terminal boundary and the growth/anchor boundary
30: are definitionally different presentations of exactly the same obligation. -/
31: theorem prolongationOrDefectAt_iff_growthAnchorProlongationAt
32:     {M : Type w} {rho : Ordinal.{0}}
33:     {W : KnightRealization (blockStage rho) M} (hW : W.IsModel) :
34:     ProlongationOrDefectAt W ↔ GrowthAnchorProlongationAt W := by
35:   unfold ProlongationOrDefectAt GrowthAnchorProlongationAt
36:   have hfinite : (∀ K : ℕ, ¬ W.IsCharacteristicArity K) ↔
37:       W.HasTopGradeGrowth := by
38:     constructor
39:     · intro hnone
40:       by_contra hgrowth
41:       obtain ⟨K, hK⟩ := hW.exists_isCharacteristicArity_iff.mpr hgrowth
42:       exact hnone K hK
43:     · intro hgrowth K hK
44:       exact (hW.exists_isCharacteristicArity_iff.mp ⟨K, hK⟩) hgrowth
45:   rw [hfinite]
46: 
47: end VaughtConjecture.Knight
```

### `VaughtConjecture/Knight/AnchorStable.lean` — lines 7–37

SHA-256: `561a56bf47f9899660d3b641054a11b2aad7177525ccc8368388274cec442658`.

```text
7: import VaughtConjecture.Knight.TopGradeStableSpectrum
8: import VaughtConjecture.Knight.ProvisionalOffset
9: 
10: /-! # Anchors at infinity are exactly the finite stable top values
11: 
12: The reviewer's notes16 §2 (2026-09-19), completing `Knight/StableAnchor.lean`
13: (`isInfinityAnchor_of_stable`: a finite stable top value is an anchor at threshold `j + 1`)
14: with the converse and the resulting equivalences.
15: 
16: * **The band forced by an anchor** (`someProvisionalValue_lt_of_anchor`): in a cover whose top
17:   grade exceeds the threshold `K'`, the strict anchor clause at the cover's full-scope top owner,
18:   taken against the anchor itself as the top source, gives `E(Θ)(∞̃) < R_{K',K'}(E(Θ)(∞̃))`, so
19:   the source has finite part `j < K'`; the cap clause fails (the cap inequality at the top grade
20:   would contradict the strict clause, replacement at a larger grade being larger), and the band
21:   is at most `j`.  Hence the provisional value is `α + j` with `j < K'`
22:   (`someProvisionalValue_le_of_anchor` in every cover).
23: * **Stabilization from a uniform bound** (`exists_stabilizesTo_of_bounded`): if the provisional
24:   values of a top cell are bounded by `α + K` on every cover, the greatest attained offset
25:   stabilizes — the ratchet only allows a value to stay or to jump above `α + K^y`, and the
26:   greatest offset is attained at a cover `y` whose `α + K^y` dominates it.
27: * **Anchor ⇒ finite stable value** (`exists_stableValue_of_anchor`,
28:   `stableValue_le_of_anchor`), and the equivalences `hasInfinityAnchor_iff_exists_finite_stable`
29:   and `isHollow_iff_stable_identity` (hollowness is exactly stable-label fixedness; the forward
30:   direction is `stableValue_eq_label_of_hollow`).
31: * **The sharp threshold, under top-grade growth only** (`lt_of_anchor_of_growth`,
32:   `isLeast_anchor_threshold`): with `HasTopGradeGrowth`, an anchor at `K'` with stable value
33:   `α + j` has `j < K'`, so `j + 1` is the least threshold.  This is stated separately from the
34:   equivalence: at finite characteristic arity, thresholds above the characteristic are vacuous
35:   (`isInfinityAnchor_succ_of_label_top`), and the sharp calculation does not hold there.
36: 
37: Construction-private (not root-exported). -/
```

### `lakefile.toml` — lines 1–36

SHA-256: `97fec44b018af06b12d584309f0d08ac75a9f3253a988534f5d14617df4edc42`.

```text
1: name = "VaughtConjecture"
2: version = "0.1.0"
3: license = "Apache-2.0"
4: keywords = ["math", "model theory", "vaught"]
5: defaultTargets = ["VaughtConjecture"]
6: 
7: [leanOptions]
8: pp.unicode.fun = true
9: autoImplicit = false
10: relaxedAutoImplicit = false
11: weak.linter.mathlibStandardSet = true
12: 
13: # Dependencies.  `InfinitaryLogic` (cameronfreer/infinitary-logic) supplies
14: # L_{ω₁,ω} syntax/semantics, Scott analysis, Morley counting, and the coding of
15: # countable models.  Mathlib is NOT required directly: it is inherited from
16: # InfinitaryLogic's manifest (currently the `cameronfreer/mathlib4` fork commit
17: # carrying the in-flight ModelTheory/Infinitary and Ordinal.lift PR stack), so
18: # the only pins are the InfinitaryLogic revision below and `lean-toolchain`,
19: # which must equal InfinitaryLogic's (checked by `scripts/check.sh`).  To bump:
20: # change `rev`, run `lake update InfinitaryLogic`, copy its `lean-toolchain`.
21: #
22: # TauCeti (TauCetiProject/TauCeti) is deliberately not required: it pins
23: # upstream mathlib, and the fork's `SetTheory/Ordinal/Family.lean` change
24: # invalidates ~2260 of its ~3050 modules, which would make every build rebuild
25: # most of TauCeti from source; it also has no model-theory content.
26: [[require]]
27: name = "InfinitaryLogic"
28: git = "https://github.com/cameronfreer/infinitary-logic"
29: rev = "261402906fce734242025f046a37ec4eec21d652"  # IL #131 merged: observation-compatible, nonempty constancy; same Lean/Mathlib
30: 
31: # Authoritative: every module under `VaughtConjecture/` (and the root) is built,
32: # whether or not the root re-exports it, so an orphan file cannot escape the
33: # build; `scripts/check.sh` likewise audits every source module.
34: [[lean_lib]]
35: name = "VaughtConjecture"
36: globs = ["VaughtConjecture.*"]
```

### `lean-toolchain` — lines 1–1

SHA-256: `cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf`.

```text
1: leanprover/lean4:v4.34.0-rc1
```

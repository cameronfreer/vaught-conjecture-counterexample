# Established literature connections and a paper plan

These connections separate standard background from the new finite construction. They do not claim that the cited papers already prove the present receiver, identify its closure with model-theoretic algebraic closure, or validate the supplied endpoint. The current implementation is documented separately in `SOURCE_AUDIT.md`.

## 1. Minimal scattered infinitary sentences

**References:** Harnik–Makkai [HM77]; Larson [Lar14], especially Remark 10.9.

The directly proved property is that every infinitary sentence has a countable truth side or false side among the base-model classes. Together with uncountability and thinness, this places the construction in the theory of minimal counterexamples/scattered infinitary sentences. Larson explicitly discusses strengthening a counterexample to a minimal one and its relationship with Scott processes.

**Application here:** make sentence minimality, produced by expansion domains, the central intermediate theorem. Do not say that the new construction establishes minimality by invoking the general reduction: it establishes it directly. Do not infer a first-order complete theory with the same spectrum.

## 2. Convex geometries and finite-character closure

**References:** Edelman–Jamison [EJ85]; Adaricheva [Ada16], Definitions 1–2 and the discussion of algebraic closure systems.

Anti-exchange closure and finitary extension are established notions. In this literature, “algebraic closure operator” means finite character, not model-theoretic `acl`.

**Application here:** the current plan equivalence and global hull theorem put the support geometry literally inside this framework, with the additional two-extreme-point restriction. That restriction must be stated: the construction does not range over all convex geometries. The new binary-operation deduction is in `HULL_ALGEBRA.md`; it is not a theorem attributed to these references. Avoid calling the property “convex dimension two,” which is different terminology.

## 3. Scott analysis and potential isomorphism

**Reference:** Larson [Lar14], especially its formula/projection and Scott-process development.

Scott analysis organizes finite-tuple information through ordinal stages. The actual interface here is bounded back-and-forth: whole finite-cover transfer yields the successor step, and the current pointed comparison API can be stated using those standard relations.

**Application here:** present comparison as a producer of ordinary partial isomorphisms, with roots retained only inside the selected extendible family. The expansion tower is not automatically the complete Scott process. Its block index is not automatically Scott rank. A paper should state the proved one-way comparison and reserve equality or full representation results for separate theorems.

## 4. Invariant separation and López–Escobar

**References:** López–Escobar [LE65]; Vaught [Vau74]; Engström–Schlicht [ES10], introduction and its proof of the invariant-definability variants.

The standard bridge identifies invariant Borel classes of countable structures with infinitary definability. In the present application, a hypothetical perfect antichain gives two disjoint invariant analytic saturations. An invariant Borel separator becomes a sentence contradicting sentence minimality.

**Application here:** use the usual model-code space and permutation action. The quotient is only a set of classes. No measurable classifying map or Borel structure on that quotient is required. This is a concrete application of the existing bridge, not a new descriptive rank theory.

## 5. Morley counting and the witnessed perfect-set alternative

**Reference:** Morley [Mor70]. The exact witnessed alternative used in the formalization is recorded in the current `Spectrum/Sentence.lean` and the pinned infinitary-logic library.

**Application here:** distinguish the theorem giving a perfect-antichain witness in the large alternative from the bare cardinal list. Thinness excludes that witnessed alternative and yields the upper bound `ℵ₁`. The lower bound is supplied by the new construction, not by Morley counting. State the perfect-set failure separately from any cardinal form requiring a failure of CH.

The original Morley paper's metadata was located, but its full text was not accessible during this review. Do not treat this bibliography check as an independent reconstruction of its proof.

## 6. Knight's earlier generalized type-space program

**Reference:** Knight [Kni07]; Knight's author-hosted preprints page, last modified 2 October 2018.

The author describes the earlier work in terms of type categories, the Morley hierarchy, and a transition from total tuple-projection maps to partial maps, followed by a reduction to a Vaughtian stack.

**Application here:** the hull interpretation now gives a direct geometric explanation of the partial maps: a subset fails to have a restricted chart because it is not closed. Cite the published 2007 paper for the historical framework, while crediting the present finite construction and formal integration separately. Do not describe the 2026 source manuscript as a newly published, externally verified paper on the strength of this record.

## What should not be promoted to a literature identification

The dense-request construction has the ordinary countable generic-construction pattern, but the present source does not need unrestricted Fraïssé amalgamation. Cap-ball lifting resembles many familiar lifting properties, but no sheaf-descent, flasqueness, model-completion, or saturation theorem has been identified and proved equivalent. Anti-exchange hulls are not matroid pregeometries. The numerical limit can be explained with monotone nets and `ℕ∞`; this does not require compactness of an arbitrary space of legal diagrams. There is no need to introduce speculative categorical vocabulary in the main paper.

## Proposed paper organization

**Suggested title:** *A thin uncountable infinitary class from labelled finite convex geometries*.

Open with the exact infinitary statement, the stronger sentence-minimality intermediate result, and a two-page dependency outline. Then separate the paper into:

1. A general theorem about continuous decreasing expansion domains, countable losses, and logical agreement; state the standard descriptive consequences here.
2. Finite convex geometry, graded semantic rows, and the precise cap-lifting lemma.
3. The actual language/sentence and countable finite-master construction.
4. Ordinary and constrained receiving: construction, installation, and readback.
5. Structural stable refinement, the three terminal comparisons, and countable terminal fibres.
6. Domain continuity, sharp one-block comparison, and independent terminal-loss witnesses.

Put characteristic theory, global stopping, detailed compatibility interfaces, and optional closure/definability consequences in appendices or companion work. Provide a theorem-to-Lean-declaration table and pinned build/audit information, distinguishing kernel checks from review that the definitions express the intended mathematics. This ordering lets the reader see exactly what the finite lemma has to accomplish before reading its technical proof.

## Bibliographic access record

The full HTML research papers [Ada16], [Lar14], and [ES10] were inspected. [EJ85], [HM77], [LE65], and [Vau74] bibliographic details and the relevant classical connections were checked through those primary research papers' statements and references, not by claiming to have read inaccessible original scans. Knight's author-hosted historical description and Oxford's bibliographic record for [Kni07] were inspected. The original journal full-text fetches for [Kni07] and [Mor70] were not usable. Stable identifiers and the corresponding records are collected in `REFERENCES.bib`.

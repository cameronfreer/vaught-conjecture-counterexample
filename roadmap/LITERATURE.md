# Established literature connections and a paper plan

These connections separate standard background from the new finite construction. They do not claim that the cited papers already prove the present receiving property, identify its closure with model-theoretic algebraic closure, or establish the main theorem.

## 1. Minimal scattered infinitary sentences

**References:** Harnik–Makkai [HM77]; Larson [Lar14], especially Remark 10.9.

The directly proved property is that every infinitary sentence has a countable truth side or false side among the base-model classes. Together with uncountability and thinness, this places the construction in the theory of minimal counterexamples/scattered infinitary sentences. Larson explicitly discusses strengthening a counterexample to a minimal one and its relationship with Scott processes.

**Application here:** make sentence minimality, produced by expansion domains, the central intermediate theorem. Do not say that the new construction establishes minimality by invoking the general reduction: it establishes it directly. Do not infer a first-order complete theory with the same spectrum.

## 2. Convex geometries and finite-character closure

**References:** Edelman–Jamison [EJ85]; Adaricheva [Ada16], Definitions 1–2 and the discussion of algebraic closure systems.

**Source of the plans:** the recursive amalgamation plans and their restriction to visible faces are Knight [Kni26], Definitions 2.1.1 and 2.1.5; their reading as two-extreme convex geometries is the formalization's.

Anti-exchange closure and finitary extension are established notions. In this literature, “algebraic closure operator” means finite character, not model-theoretic `acl`.

**Application here:** the current plan equivalence and global hull theorem put the support geometry literally inside this theory, with the additional two-extreme-point restriction. That restriction must be stated: the construction does not range over all convex geometries. The new binary-operation deduction is in `HULL_ALGEBRA.md`; it is not a theorem attributed to these references. Avoid calling the property “convex dimension two,” which is different terminology.

## 3. Scott analysis and potential isomorphism

**References:** Scott [Sco65]; Karp [Kar65]; Larson [Lar14], especially its formula/projection and Scott-process development.

Scott analysis [Sco65] organizes finite-tuple information through ordinal stages. Agreement on all sentences of quantifier rank at most \(\alpha\) is characterized by back-and-forth systems of length \(\alpha\) [Kar65]. The actual interface here is bounded back-and-forth: whole finite-cover transfer yields the successor step, and the current pointed comparison API can be stated using those standard relations.

**Application here:** present comparison as a construction of ordinary partial isomorphisms, with roots retained only inside the selected extendible family. The expansion tower is not automatically the complete Scott process. Its block index is not automatically Scott rank. A paper should state the proved one-way comparison and reserve equality or full representation results for separate theorems.

## 4. Invariant separation and López–Escobar

**References:** López–Escobar [LE65]; Vaught [Vau74]; Engström–Schlicht [ES10], introduction and its proof of the invariant-definability variants.

The standard bridge identifies invariant Borel classes of countable structures with infinitary definability. In the present application, a hypothetical perfect antichain gives two disjoint invariant analytic saturations. An invariant Borel separator becomes a sentence contradicting sentence minimality.

**Application here:** use the usual model-code space and permutation action. The quotient is only a set of classes. No measurable classifying map or Borel structure on that quotient is required. This is a concrete application of the existing bridge, not a new descriptive rank theory.

## 5. Counting by Scott separation, and Morley counting as an alternative not used

**References:** Harnik–Makkai [HM77]; Larson [Lar14], Remark 10.9. For the alternative that is not used: Morley [Mor70].

**Application here:** the upper bound `ℵ₁` is a counting argument in the setting of minimal counterexamples of [HM77] (see [Lar14], Remark 10.9, and its discussion of minimal counterexamples); [HM77] is cited for that setting, not as the source of this exact argument. The expansion domains have countable complements, and Scott separation (distinct classes are separated by a sentence) together with agreement on the domains leaves at most one class in every domain, so the classes are covered by one point and `ℵ₁` many countable sets. Thinness is proved separately, from the countable truth sides, by the pinned infinitary-logic library's thinness theorem for countable sentence splits (`Sentenceω.isThinOnNatModels_of_countable_sentence_splits`). Morley's theorem, in the witnessed form that gives a perfect antichain in the large alternative, would also yield the upper bound from thinness; that route is not used. The lower bound is supplied by the new construction, not by a counting theorem. State the perfect-set failure separately from any cardinal form requiring a failure of CH.

The original Morley paper's metadata was located, but its full text was not accessible during this bibliography check. Do not treat this bibliography check as an independent reconstruction of its proof.

## 6. Knight's earlier generalized type-space program

**Reference:** Knight [Kni07]; Knight's author-hosted preprints page, last modified 2 October 2018.

The author describes the earlier work in terms of type categories, the Morley hierarchy, and a transition from total tuple-projection maps to partial maps, followed by a reduction to a Vaughtian stack.

**Application here:** the hull interpretation now gives a direct geometric explanation of the partial maps: a subset fails to have a restricted chart because it is not closed. Cite the published 2007 paper for the historical program, while crediting the present finite construction and formal integration separately. Do not describe the 2026 source manuscript as a newly published, externally verified paper on the strength of this record.

## What should not be promoted to a literature identification

The dense-request construction has the ordinary countable generic-construction pattern, but the present source does not need unrestricted Fraïssé amalgamation. Cap-ball lifting resembles many familiar lifting properties, but no sheaf-descent, flasqueness, model-completion, or saturation theorem has been identified and proved equivalent. Anti-exchange hulls are not matroid pregeometries. The numerical limit can be explained with monotone nets and `ℕ∞`; this does not require compactness of an arbitrary space of legal diagrams. There is no need to introduce speculative categorical vocabulary in the main paper.

## Proposed paper organization

**Suggested title:** *A thin uncountable infinitary class from labelled finite convex geometries*.

Open with the exact infinitary statement, the stronger sentence-minimality intermediate result, and a two-page dependency outline. Then separate the paper into:

1. A general theorem about continuous decreasing expansion domains, countable losses, and logical agreement; state the standard descriptive consequences here.
2. Finite convex geometry, graded semantic rows, and the precise cap-lifting lemma.
3. The actual language/sentence and countable finite-master construction.
4. Ordinary and constrained receiving: the finite construction, realization over the root, and recovery of donor labels.
5. Structural stable refinement, the three terminal comparisons, and countable terminal fibres.
6. Domain continuity, sharp one-block comparison, and independent terminal-loss witnesses.

Put characteristic theory, global stopping, detailed compatibility interfaces, and optional closure/definability consequences in appendices or companion work. Provide a theorem-to-Lean-declaration table and pinned build/audit information, distinguishing kernel checks from the human check that the definitions express the intended mathematics. This ordering lets the reader see exactly what the finite lemma has to accomplish before reading its technical proof.

## Bibliographic access record

The full HTML research papers [Ada16], [Lar14], and [ES10] were inspected. [Kni26] is the draft manuscript of the construction itself (Definitions 2.1.1 and 2.1.5 cited for the plans). [EJ85], [HM77], [LE65], and [Vau74] bibliographic details and the relevant classical connections were checked through those primary research papers' statements and references, not by claiming to have read inaccessible original scans. [Sco65] and [Kar65] are cited from their standard bibliographic records in the proceedings of the 1963 Berkeley symposium; their full texts were not re-inspected for this document. Knight's author-hosted historical description and Oxford's bibliographic record for [Kni07] were inspected. The original journal full-text fetches for [Kni07] and [Mor70] were not usable. Stable identifiers and the corresponding records are collected in `REFERENCES.bib`.

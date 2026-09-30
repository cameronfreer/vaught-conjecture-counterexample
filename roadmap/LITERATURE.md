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

## 7. The companion milestones

**References:** Scott [Sco65]; Karp [Kar65]; Harnik–Makkai [HM77]; Larson [Lar14]; Marker [Mar02], Chapter 4.

**Application here:** the companion milestones of `COMPANIONS.md` rely on standard background only. In milestone A, the sentences defining countable or cocountable sets of classes are countable disjunctions of Scott sentences [Sco65], and the rank lower bound for a sentence defining a loss is read through agreement at bounded quantifier rank, characterized by back-and-forth systems [Kar65]. The set `T∞` of sentences true in all but countably many classes belongs to the setting of minimal counterexamples [HM77] (see [Lar14] and its discussion of minimal counterexamples); these are cited for that setting, not as the source of the witness convergence or of the Scott/`T∞` dichotomy as stated there. In milestone B, isolated types, atomic models, and the theorem that a countable atomic model is prime are standard first-order model theory [Mar02, Chapter 4]; the internal Scott rank follows the convention of the pinned infinitary-logic library. The amalgamation of top-free charts, now part of the core, is the amalgamation property of the age of top-free charts in the definitional expansion by the hull operations; it is a theorem about labelled finite charts, not a known amalgamation class of the literature (§8). No literature identification is claimed for the geometric obstruction of milestone C.

## 8. Fraïssé limits, atomic and prime models, and back-and-forth

**References:** Fraïssé [Fra54]; Hodges [Hod93], Chapter 7, §7.1; Vaught [Vau61]; Marker [Mar02], Chapter 4; Karp [Kar65]; Larson [Lar14] for Scott processes.

These are the classical sources of the construction of the top-free witnesses (`README.md`, the section on the top-free witnesses after Layer 3) and of the companion orbit theory (`COMPANIONS.md`, milestone B). A class of finitely generated structures with countably many isomorphism types and the hereditary, joint embedding, and amalgamation properties, in a countable language, is the age of a countable ultrahomogeneous structure, unique up to isomorphism: its Fraïssé limit [Fra54; Hod93, §7.1]. Ultrahomogeneity of a countable structure is the extension property of its finitely generated substructures, and uniqueness is a back-and-forth argument [Hod93, §7.1]; agreement at bounded quantifier rank is characterized by bounded back-and-forth [Kar65]. A complete type is isolated when one formula implies it modulo the theory, a model is atomic when every finite tuple realizes an isolated type, and a countable atomic model is prime, embedding elementarily into every model of its complete theory [Vau61; Mar02, Chapter 4]. The formal statements used are Mathlib's Fraïssé interface and the theorems of the computable-model-theory library (ComputableModelTheory) and the infinitary-logic library (InfinitaryLogic) listed in `README.md`, Layer 0.

**Application here, with its qualifications.**

- The age is that of the finite top-free charts in the definitional expansion of the stage chart language by the hull operations (`README.md`, Layer 2). Without the expansion, a finite subset that is not closed is a substructure with no chart, and the finite substructures of the relational structure are not the charts. The amalgamation property of this age is a theorem about labelled finite charts, proved from the coatom extension property; it is not identified with a known amalgamation class of the literature, and it is not strong amalgamation.
- Isolation, atomicity, and primeness concern a top-free witness in the full stage chart language and its own complete first-order theory; they say nothing by themselves about its base reduct or about the other models of the infinitary sentence. "Atomic" means that complete types are isolated, not that formulas are syntactically atomic. Primeness is for the complete first-order theory, not for an infinitary theory.
- Rank conventions: the internal Scott rank is the all-levels convention of InfinitaryLogic, the supremum of the orbit ranks plus one; orbit formulas give a bound at most \(\omega\), not below \(\omega\), and not an equality. The rank of the Scott process [Lar14] is compared with it only through the precise two-sided comparison of InfinitaryLogic, for a relational language and an infinite structure, with stabilization at \(\omega\) requiring a process of length \(\delta\) with \(\omega+1<\delta\); the two ranks are not identified, and neither is identified with the block index or the expansion height.
- Classical existence uses choice and gives no computable enumeration of the limit; in this development it is an intended dependency of ComputableModelTheory, to be quoted after the repin (`IMPLEMENTATION.md`, "Dependency pins").

**Where [Kni26] differs.** [Kni26, Proposition 4.4.5] builds, at every countable limit stage, a countable saturated model in the sense of [Kni26, Definition 4.1.1], by the recursive method of amalgamating in all possible one-point extensions of each tuple; it is a model with top labels that realizes every one-point coface exactly. The lower bound of [Kni26] (Corollary 11.1.4) chooses saturated models that do not expand, which rests on [Kni26, Corollary 11.1.2] and hence on the expansion theory of its Chapter 5 (Corollary 5.5.6). The age route replaces both: existence is the classical theorem applied to the age of top-free charts, whose amalgamation is proved directly for finite charts before any infinite model exists, and the witnesses of the lower bound are top-free, so they are terminal by top-freeness and their base classes lie in the losses by expansion uniqueness. The saturated model of [Kni26, Proposition 4.4.5] remains a statement of the retained chain construction, outside the main theorem.

## What should not be promoted to a literature identification

The top-free witnesses are ordinary Fraïssé limits of the age of top-free charts in the definitional expansion (§8), but the example as a whole is not a Fraïssé limit: models with top labels are not limits of that age, and their classification (stable continuation, the LOW decoding, the terminal comparisons, the countability of terminal classes) is not reduced to Fraïssé theory. Cap-ball lifting resembles many familiar lifting properties, but no sheaf-descent, flasqueness, model-completion, or saturation theorem has been identified and proved equivalent. Anti-exchange hulls are not matroid pregeometries. The numerical limit can be explained with monotone nets and `ℕ∞`; this does not require compactness of an arbitrary space of legal diagrams. There is no need to introduce speculative categorical vocabulary in the main paper.

## Proposed paper organization

**Suggested title:** *A thin uncountable infinitary class from labelled finite convex geometries*.

Open with the exact infinitary statement, the stronger sentence-minimality intermediate result, and a two-page dependency outline. Then separate the paper into:

1. A general theorem about continuous decreasing expansion domains, countable losses, and logical agreement; state the standard descriptive consequences here.
2. Finite convex geometry, graded semantic rows, and the precise cap-lifting lemma.
3. The actual language/sentence, the hull operations, and the top-free witnesses as reconstructed Fraïssé limits of the age of top-free charts.
4. Ordinary and constrained receiving: the finite construction, realization over the root, and recovery of donor labels.
5. Structural stable refinement, the three terminal comparisons, and countable terminal fibres.
6. Domain continuity, sharp one-block comparison, and independent terminal-loss witnesses.

Put characteristic theory, global stopping, detailed compatibility interfaces, and optional closure/definability consequences in appendices or companion work. Provide a theorem-to-Lean-declaration table and pinned build/audit information, distinguishing kernel checks from the human check that the definitions express the intended mathematics. This ordering lets the reader see exactly what the finite lemma has to accomplish before reading its technical proof.

## Bibliographic access record

The full HTML research papers [Ada16], [Lar14], and [ES10] were inspected. [Kni26] is the draft manuscript of the construction itself (Definitions 2.1.1 and 2.1.5 cited for the plans). [EJ85], [HM77], [LE65], and [Vau74] bibliographic details and the relevant classical connections were checked through those primary research papers' statements and references, not by claiming to have read inaccessible original scans. [Sco65] and [Kar65] are cited from their standard bibliographic records in the proceedings of the 1963 Berkeley symposium; their full texts were not re-inspected for this document. [Mar02] is cited from its standard bibliographic record; its text was not re-inspected for this document. [Fra54], [Hod93], and [Vau61], cited in §8 for the classical theory of Fraïssé limits and of atomic and prime models, are cited from their standard bibliographic records (for [Hod93], the publisher's chapter record of Chapter 7); their texts were not re-inspected for this document. Knight's author-hosted historical description and Oxford's bibliographic record for [Kni07] were inspected. The original journal full-text fetches for [Kni07] and [Mor70] were not usable. Stable identifiers and the corresponding records are collected in `REFERENCES.bib`.

Beyond the plans, the roadmap cites [Kni26] for Definitions 2.2.3, 2.3.4, 2.3.9, 2.5.3, 2.5.4, 2.5.12, 2.5.14, 2.5.15, 2.6.1, 3.1.1, 3.1.5, 3.2.1, 4.1.1, 4.3.1, 4.3.3, 4.3.5, 4.3.6, 4.3.7, 4.3.14, and 8.3.1, Lemmas 2.2.4, 2.5.8, 4.3.2, 4.3.20 (its statement is unproved and not relied on; neither is its printed proof, which applies the joint lifting of Lemma 4.3.19), 4.4.3, 5.3.5, and 8.1.1 (whose proof cites high-arity dominance as clause 4(a) of Definition 3.2.1, where it is clause 4(c)), Corollary 4.3.22 and Proposition 4.3.23 (their statements, used at stages that are zero or limits; the printed proof of 4.3.22, through Lemmas 4.3.19–4.3.21 and a truncation valid only at such stages, is not relied on), Proposition 4.3.24, Proposition 4.4.5 and Corollaries 5.5.6, 11.1.2, and 11.1.4 (the saturated model and the manuscript's lower bound, compared with the age route in §8), and §2.5 (the finite semantics and the constructions), and for Lemmas 2.3.10 (the floor formula of its proof), 2.3.14, 2.5.7, 2.5.9, 2.5.11, 2.5.13, and 3.1.3 (the shifter displayed in its proof), printed statements that are not correct as stated and are not relied on. Lemma 4.3.19 is not relied on either: its conclusions 1–3 cannot hold together under the natural readings of efficiency (Definition 4.3.6, whose bindings the text leaves open), since an instance with cap 2 and prescriptions 3 and 4 forces 3 = 4. The bountifulness of the completion of Definition 4.3.14 (the statement of Lemma 4.3.20; Definitions 4.3.3, 4.3.5, 4.3.6, and 4.3.7 give its cells, and Definition 4.3.6 needs explicit bindings before that statement is definite) is unproved, not refuted; the roadmap proves the bountifulness of the completion it constructs instead (`README.md`, Layer 3, 3.1, row 6). These were checked against the same draft.

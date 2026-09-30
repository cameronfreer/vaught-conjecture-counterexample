<!-- One topic per PR.  Name the layer of roadmap/README.md (Layers 0–6) this advances, e.g.
     `Roadmap: Layer 3`, or `Roadmap: none`. -->
Roadmap: 

## Summary



## Checklist

- [ ] `lake build && bash scripts/check.sh --no-build` passes locally (paste the axiom-audit line)
- [ ] Statements checked against `roadmap/SEMANTIC_CONTRACT.md`; new declarations reuse Mathlib /
      InfinitaryLogic where they exist (name what was searched for)
- [ ] Docstrings say what each statement gives; no wrappers, aliases, or compatibility shims
- [ ] Mathematical terminology only in names, docstrings, and prose (no producer/consumer/
      supplier/receipt/certificate vocabulary; see `roadmap/README.md`, "Library conventions")

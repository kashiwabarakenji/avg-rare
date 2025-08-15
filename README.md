# Avg-Rare Formalization (Lean 4)

This repository is a clean, paper-aligned Lean 4 formalization template
for functional preorders and the Average-Rare (Frankl-type) results.

## Structure
- `AvgRare/Basics/` — Core definitions (`Nds`, `Trace`, `Excess`).
- `AvgRare/SPO/` — Functional preorder structures (`SetupSpo`, `Spo2`) and translations.
- `AvgRare/Forests/` — Induction on rooted forests, direct product lemmas.
- `AvgRare/PaperSync/` — Thin wrappers matching paper numbering.
- `specs/` — Natural-language definitions/specs used to drive code generation.
- `tests/` — Tiny finite examples for sanity checks.
- `.github/workflows/ci.yml` — CI build on GitHub Actions.

## Build
```bash
lake build
```

## Run tests (example executable placeholder)
```bash
lake exe tests
```

## Notes
- This template mirrors the paper's structure; add your SpecBlocks and implementations step by step.
- The `lakefile.lean` includes mathlib and LeanCopilot (v4.21.0) like your current project,
  and passes through `-lctranslate2` for Copilot's native extension.

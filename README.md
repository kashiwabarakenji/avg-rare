# Avg-Rare Formalization (Lean 4)

This repository contains a Lean 4 formalization of functional preorders and Average-Rare (Frankl-type) results with complete English documentation.

## Structure
- `AvgRare/Basics/` — Core definitions (`SetFamily`, `SetTrace`, general lemmas).
- `AvgRare/Functional/` — Functional preorder structures (`FuncSetup`, `FuncPoset`, `TraceFunctional`).
- `AvgRare/Reductions/` — Reduction theorems (`Rare`, `Reduction`).
- `AvgRare/Secondary/` — Secondary theorems (`MainStatement`, `SumProduct`, `UniqueMax`).
- `AvgRare/Old/` — Legacy code (not part of current formalization).
- `specs/` — Natural-language definitions/specs.
- `tests/` — Small finite examples for verification.

## Key Features
- **Complete English Documentation**: All comments and documentation are in English for international collaboration
- **Mathematical Rigor**: Formal verification of Average-Rare theorems using Lean 4
- **Modular Structure**: Clean separation of basic definitions, functional structures, and main results
- **Paper Alignment**: Structure follows the mathematical development in the research papers

## Build
```bash
lake build
```

## Run tests
```bash
lake exe tests
```

## Main Results
The formalization includes proofs of:
- **Trace Operations**: Formal verification of trace reductions and their properties
- **Functional Family Properties**: Preservation of functional structure under various operations  
- **Rareness Theorems**: Key results about rare elements in set families
- **Reduction Arguments**: Main theorems connecting functional preorders to Average-Rare bounds

## Notes
- All code comments and documentation are in English for international accessibility
- The formalization uses Lean 4 with mathlib for mathematical foundations
- Structure follows the paper's mathematical development with formal verification

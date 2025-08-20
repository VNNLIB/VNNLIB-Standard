# Contributing to VNNLIB

⚠️ Work-in-Progress: This repository contains an early-stage proposal for VNNLIB-2.0, that is constantly being refined.

Thanks for your interest in improving the VNNLIB project! This guide explains the tools we use, how the repo is structured, how to build & test things locally, and what we expect in pull requests.
If anything here is unclear, please open an issue so we can improve this doc.

## Repository layout
```
.
├── syntax.cf           # LBNF grammar for VNNLIB 2.0
├── document/           # .tex files for VNNLIB specification document
├── parser_cpp/         # C++ library (parser + typechecker)
│ └── test/             # Unit tests and golden tests
| └── cpp/              # C++ source code
| └── python/           # Python library
|   └── vnnlib/         # Python bindings + stub files
|   └── setup.py        # Build instructions
├── build_parser.sh     # Build entrypoint
├── test.sh             # Test harness for grammar
└── CONTRIBUTING.md     # This guide
```

## Syntax
The formal syntax of the VNNLIB-2.0 language is located in `syntax.cf`. This syntax uses the Labelled Backus Neur Formalism (LBNF), which is compiled by BNFC to produce a parser and lexer.
To compile the grammar, [BNFC](https://hackage.haskell.org/package/BNFC) must be installed

### 1. Build the Haskell-based parser
```bash
$ bnfc -d -m syntax.cf  &&  make
```

### 2. Run tests against example queries
A set of example queries are located in the `test/` folder.
These examples are adapted from the [VNNLIB Benchmarks Repository](https://github.com/VNNLIB/Benchmarks/) or composed manually as valid queries.

To run tests with the Haskell-based parser:
```bash
$ Syntax/Test <path-to-test-file>
```

Example `.vnnlib` files live under `test/` (sourced from the VNNLIB Benchmarks repo or hand-written). Run the generated test driver:

```bash
$ chmod +x test.sh
$ ./test.sh
```

## Parser (C++ and Python)

### Quickstart
#### 1. Set up a Python venv
```bash
python -m venv .venv && source .venv/bin/activate
pip install -U pip
```
#### 2. Build parser and run tests
``` bash
chmod +x build_parser.sh
./build_parser.sh           # Build C++ source and Python wheel
./build_parser.sh test      # run pytest
```

### Testing
We value tests that are minimal and readable. Consider using a framework such as Input Space Partitioning for efficient coverage.

### Performance tests
- Tests measure the end-to-end parse+typecheck throughput on a VNNLIB-2.0 converted version of the 2025 VNNCOMP Collins Aerospace benchmark.
- Performance should not regress by >10% on CI runners

### Error model
Errors raised by the parser and typechecker have a JSON shape to make tests deterministic. For instance:
```json
{
  "errors": [
    {
      "message": "Duplicate variable declaration",
      "offendingSymbol": "X",
      "hint": "Variable names must be unique within the specification",
      "errorCode": "MultipleDeclaration"
    }
  ]
}
```

## Contribution workflow
1. Create an issue referencing the feature to be added (or bug to be fixed)
1. **Fork** the repo and create a feature branch, linking it to the created issue
2. Make focused commits that contain a prefixed issue number.
3. Ensure local checks pass:
   - `./test.sh` (grammar)
   - `./build_parser.sh` and `./build_parser.sh test` (parser + tests)
4. Open a **pull request** with:
   - Description of the change and motivation
   - Benchmarks if it touches performance-critical code
   - Tests for new behavior.
   - Updated documentation if relevant.
5. Squash/clean up commits if asked.

## Issue filing convention
Please include
- **Environment**
- **Minimal reproducible example**: Smallest `.vnnlib` reproducing the problem.
- **Expected behaviour vs actual**
- **Log output**: Stack traces.

## Roadmap & where to help
- Docs site with examples and a tutorial
- Windows/macOS integration
- Adding lint rules to CI
- Modifying C++ library to apply RAII concepts: use std::unique_ptr in place of new/delete
- Issues in the `spec-future milestone`
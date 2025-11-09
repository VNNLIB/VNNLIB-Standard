# Contributing to VNNLIB

⚠️ Work-in-Progress: This repository contains an early-stage proposal for VNNLIB-2.0, that is constantly being refined.

Thanks for your interest in improving the VNNLIB project! This guide explains how the repo is structured, and how to build and test the grammar.

## Repository layout
```
.
├── syntax.cf           # LBNF grammar for VNNLIB 2.0
├── document/           # .tex files for VNNLIB specification document
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

## Issue filing convention
Please include
- **Environment**
- **Minimal reproducible example**: Smallest `.vnnlib` reproducing the problem.
- **Expected behaviour vs actual**
- **Log output**
# Contributing to VNNLIB

Thanks for your interest in improving the VNNLIB project! This guide explains how the repo is structured, and how to build and test the grammar.

## Repository layout
```
.
├── document/           # .tex files for VNNLIB specification document
└── syntax/             # official formal syntax for the VNNLIB query language
  ├── grammar.cf          # LBNF grammar for VNNLIB 2
  ├── test.sh             # Test harness for grammar
  ├── tests/              # Test cases
  └── CONTRIBUTING.md     # This guide
```

## Syntax

The formal syntax of the VNNLIB language is located in `syntax/grammar.cf`. This syntax uses the Labelled Backus-Naur Formalism (LBNF), which is compiled by BNFC to produce a parser and lexer.
To compile the grammar, [BNFC](https://hackage.haskell.org/package/BNFC), Alex and Happy must be installed (see `Installing bnfc and dependencies` command in `.github/workflows/` file for the exact command to install these.)

### 1. Enter the Syntax folder
```bash
cd syntax
```

### 2. Build the Haskell-based parser
```bash
bnfc -d -m grammar.cf  &&  make
```

### 3. Run tests against example queries
A set of example queries are located in the `test/` folder.
These examples are adapted from the [VNNLIB Benchmarks Repository](https://github.com/VNNLIB/Benchmarks/) or composed manually as valid queries.

To run tests with the Haskell-based parser:
```bash
Grammar/Test <path-to-test-file>
```

Example `.vnnlib` files live under `test/` (sourced from the VNNLIB Benchmarks repo or hand-written). Run the generated test driver:

```bash
chmod +x test.sh
./test.sh
```

## Issue filing convention
Please include
- **Environment**
- **Minimal reproducible example**: Smallest `.vnnlib` reproducing the problem.
- **Expected behaviour vs actual**
- **Log output**
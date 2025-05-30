# VNNLIB-Standard 

⚠️ Work-in-Progress: This repository contains an early-stage proposal for VNNLIB-2.0, an extension and refinement of the current VNNLIB specification. 

## Syntax

The formal syntax of the VNNLIB-2.0 language is located in `syntax.cf`. This syntax uses the [Labelled Backus Neur Formalism (LBNF)](https://bnfc.readthedocs.io/en/latest/lbnf.html)

This project uses the BNFC package to build a parser for testing the grammar. For installation and usage instructions, refer to the official documentation [here](https://hackage.haskell.org/package/BNFC-2.9.5).

### 1. Build the haskell-based parser
```bash
$ bnfc -d -m syntax.cf  &&  make
```

### 2. Test the parser
A set of example queries are located in the `test/` folder.
These examples are adapted from the [VNNLIB Benchmarks Repository](https://github.com/VNNLIB/Benchmarks/) or composed manually as valid queries.

To run tests with the Haskell-based parser:
```bash
$ Syntax/Test <test-file-path>
```

A Bash script `test.sh` is provided to simplify building and testing the grammar parser. It will run tests on all files located in the test/ directory.
If test.sh does not have execution permissions, add them with:

```bash
$ chmod +x test.sh
```

## Parser
The Parser provides tools to parse `.vnnlib` files. It consists of a core C library for parsing, C++ wrapper classes that create an object-oriented AST from the C structs, and Pybind11 bindings to expose this functionality to Python. The Python module allows users to load a VNNLib file, traverse its AST, view a string representation of each AST node, and check the semantic validity of the VNNLib file. An example script showing the usage of the library is `parser/pybind/test_vnnlib.py`.

A bash script `build_parser.sh` script has been provided for simplifying the build process,

If `build_parser.sh` does not have execution permissions, add them with:

```bash
$ chmod +x build_parser.sh
```

To install the `vnnlib` Python package to your local Python environment, run this command inside of `parser/pybind/`:

```bash
$ pip install .
```

## Semantics
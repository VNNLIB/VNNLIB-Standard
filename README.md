# VNNLIB-Standard 

⚠️ Work-in-Progress: This repository contains a draft proposal for the unreleased VNNLIB-2.0 standard.

The VNNLIB standard provides:

1. a standard syntax and semantics for satisfiability queries to neural network solvers
2. a standard command-line-interface for neural network verifiers

with the aim of greater interoperability and rigour in the formal verification of neural networks.
See the official [VNNLIB website](https://www.vnnlib.org/) for more details, including tooling for
interacting with the specification.

### Contents

This repository contains:
- `document/main.tex` - the standard document 
- `syntax.cf` - a formal grammar for VNNLIB queries written in Labelled Backus-Naur Form.

There are official libraries for parsing VNNLIB queries available in a variety of languages:
 - [Python](https://github.com/VNNLIB/VNNLIB-Python)
 - [C++](https://github.com/VNNLIB/VNNLIB-CPP)
 - [Julia](https://github.com/VNNLIB/VNNLIB.jl)
 - [Agda](https://github.com/VNNLIB/VNNLIB-Agda)

The [Agda](https://github.com/VNNLIB/VNNLIB-Agda) library also contains a mechanised semantics for the query language.

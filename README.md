# VNNLIB-Standard 

⚠️ Work-in-Progress: This repository contains an early-stage proposal for VNNLIB-2.0

VNNLIB-2.0 defines a more expressive, rigorous, and ergonomic standard for the verification of neural networks, building on the VNNLIB specification format. The motivation is to 
rigorously define a standard query language and CLI for verifiers, aiming for greater interoperability of the verification space. This repository contains:
- A formal grammar written in LBNF (Labelled Backus-Naur Form), used by BNFC to generate an Abstract Syntax Tree and parser
- A standard command-line interface for verifiers, described in the specification document
- A production-grade C++ parser and typechecker with Python bindings.
- VNNLIB semantics described in Agda

### Quick start

Clone and run the set-up script for parser:

```bash
# C++ core + Python bindings
./build_parser.sh
./build_parser.sh test
```

## Usage of VNNLIB-2.0
### Minimal .vnnlib example
```lisp
(declare-network acc
  (declare-input  X Real [3])
  (declare-output Y Real [1])
)
(assert (or (<= Y[0] -3.0) (>= Y[0] 0.0)))
```
A wider variety of examples can be viewed in the LaTeX document inside of `document/`

### Python parsing
```python
import json
import vnnlib

with open("examples/min.vnnlib", "r") as f:
    src = f.read()

try:
    ast = vnnlib.parse_vnnlib_str(src)   # or: vnnlib.parse_vnnlib_file("examples/min.vnnlib")
    # ..do something with AST
except vnnlib.VNNLibError as e:
    # The exception string is JSON with a stable schema
    print(json.loads(str(e)))
```

## Additional Information

### Roadmap for future spec
- Add quantifiers to the query language
- Add trigonometric functions to query language
- Extend the standard with a standard format for proofs of UNSAT
- Extend the query language with (check-sat) and (get-model) to allow incremental solving ala SMTLIB
- Extend grammar: Including complex number access operations

### Community
- Issues: use GitHub Issues with a minimal reproducible .vnnlib example
- Contributing: see [CONTRIBUTING.md](https://github.com/VNNLIB/VNNLIB-Standard/blob/main/CONTRIBUTING.md)


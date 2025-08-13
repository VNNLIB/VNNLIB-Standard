"""
VNNLib Python Bindings

Modern Python bindings for the VNNLib verification language parser and semantic analyzer.
Built with pybind11 for direct access to the BNFC-generated C++ AST.

Key Features:
- Direct C++ AST access with zero-copy performance
- Complete VNNLIB language support
- Built-in semantic analysis and type checking
- Pythonic API with full type hints
- Modern packaging with PEP 517/518 support

Basic Usage:
    import vnnlib
    
    # Parse a VNNLIB file
    query = vnnlib.parse_vnnlib("path/to/file.vnnlib")
    
    # Access networks and constraints
    for network in query.networks:
        print(f"Network: {network.variable_name}")
    
    # Semantic validation
    result = vnnlib.check_query(query)
    if result['success']:
        print("✓ Valid VNNLIB query")
"""

# Import all symbols from the compiled module
from ._core import *

# Module metadata
__version__ = "1.0.0-dev"
__author__ = "Allen Antony" 
__description__ = "Python bindings for VNNLib verification language"
__url__ = "https://github.com/VNNLIB/VNNLIB-Standard"

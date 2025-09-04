"""
VNNLib Python Bindings

Modern Python bindings for the VNNLib verification language parser.
Built with pybind11 for direct access to the BNFC-generated C++ AST.

Basic Usage:
    import vnnlib
    
    # Parse a VNNLIB file
    query = vnnlib.parse_vnnlib("path/to/file.vnnlib")
    
    # Access networks and constraints
    for network in query.networks:
        print(f"Network: {network.variable_name}")
"""

# Import all symbols from the compiled module
from ._core import *

# Module metadata
__version__ = "0.0.1-dev"
__author__ = "Allen Antony" 
__description__ = "Python bindings for VNNLib verification language"
__url__ = "https://github.com/VNNLIB/VNNLIB-Standard"

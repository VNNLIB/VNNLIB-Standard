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
        print(f"Network: {network.name}")
        
    # Use compatibility module for reachability format
    import vnnlib.compat
    cases = vnnlib.compat.transform(query)
"""

from ._core import (
    # Parsing functions
    parse_vnnlib, parse_vnnlib_str,
    
    # Core AST node types
    Query, Network, Assertion,
    InputDefinition, OutputDefinition, HiddenDefinition,
    Version,
    
    # Expression types
    ArithExpr, BoolExpr, 
    Var, Literal, Float, Int, Negate, Plus, Minus, Multiply,
    Compare, GreaterThan, GreaterEqual, LessThan, LessEqual, Equal, NotEqual,
    Connective, And, Or,
    
    # Linear arithmetic
    LinearArithExpr, Term,
    
    # Enums and data types
    DType, SymbolKind,
    
    # Exceptions
    VNNLibException,
)

# Module metadata
__version__ = "0.0.1-dev"
__author__ = "Allen Antony" 
__description__ = "Python bindings for VNNLib verification language"
__url__ = "https://github.com/VNNLIB/VNNLIB-Standard"

__all__ = [
    # Parsing functions
    "parse_vnnlib", "parse_vnnlib_str",
    
    # Core AST nodes
    "Query", "Network", "Assertion", 
    "InputDefinition", "OutputDefinition", "HiddenDefinition",
    "Version",
    
    # Expression types  
    "ArithExpr", "BoolExpr",
    "Var", "Literal", "Float", "Int", "Negate", "Plus", "Minus", "Multiply",
    "Compare", "GreaterThan", "GreaterEqual", "LessThan", "LessEqual", "Equal", "NotEqual",
    "Connective", "And", "Or",
    
    # Linear arithmetic
    "LinearArithExpr", "Term",
    
    # Enums and data types
    "DType", "SymbolKind",
    
    # Exceptions
    "VNNLibException",
]

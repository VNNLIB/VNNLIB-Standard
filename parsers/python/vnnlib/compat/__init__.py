"""
VNNLib Compatibility Module

This module provides classes and functions for converting VNNLib specifications
to reachability format compatible with reachability analysis tools.

The reachability format represents verification problems as:
1. Input constraints as box bounds (lower/upper bounds per input dimension)  
2. Output constraints as polytopes in the form Ay ≤ b
"""

from .._core import Polytope, SpecCase, transform_to_compat

__all__ = [
    "Polytope",
    "SpecCase", 
    "transform",
]

def transform(query):
    """
    Transform a VNNLib Query to reachability format.
    
    This function converts VNNLib specifications into a list of reachability cases.
    Each case consists of:
    1. Input box bounds: lower and upper bounds for each input dimension
    2. Output polytopes: constraints in the form Ay ≤ b representing disjunctions
    
    Parameters
    ----------
    query : vnnlib.Query
        The parsed VNNLib Query object to transform
        
    Returns
    -------
    List[SpecCase]
        A list of reachability cases with input bounds and output constraints
        
    Raises
    ------
    VNNLibException
        If the specification cannot be converted to reachability format.
        
    Example
    -------
    >>> import vnnlib
    >>> import vnnlib.compat
    >>> query = vnnlib.parse_vnnlib_str(content)
    >>> cases = vnnlib.compat.transform(query)
    >>> case = cases[0]
    >>> print(f"Input bounds: {case.input_box}")
    >>> print(f"Output polytopes: {len(case.output_constraints)}")
    """
    return transform_to_compat(query)
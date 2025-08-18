#!/usr/bin/env python3
"""Test script to iterate over all nodes in test/acc.vnnlib and print them."""

import sys
import os

try:
    import vnnlib
    
    # Parse the acc.vnnlib file
    test_file = "test/acc.vnnlib"
    print(f"Parsing {test_file}...")
    print("=" * 60)
    
    query = vnnlib.parse_vnnlib(test_file)
    print(f"✓ Parsed successfully: {type(query)}")
    print()
    
    # Print top-level query information
    print("TOP-LEVEL QUERY:")
    print(f"  Query type: {type(query)}")
    print(f"  Networks count: {len(query.networks)}")
    print(f"  Assertions count: {len(query.assertions)}")
    print()
    
    # Iterate over networks
    print("NETWORKS:")
    for i, network in enumerate(query.networks):
        print(f"  Network {i}: {type(network)}")
        print(f"    Variable name: {network.variable_name}")
        print(f"    String representation: {network}")
        print()
        
        # Network inputs
        print(f"    INPUTS ({len(network.inputs)}):")
        for j, inp in enumerate(network.inputs):
            print(f"      Input {j}: {type(inp)}")
            print(f"        String: {inp}")
            if hasattr(inp, 'variable_name'):
                print(f"        Variable name: {inp.variable_name}")
            if hasattr(inp, 'elementtype'):
                print(f"        Element type: {inp.elementtype}")
            if hasattr(inp, 'tensorshape'):
                print(f"        Tensor shape: {inp.tensorshape}")
            if hasattr(inp, 'string'):
                print(f"        String field: {inp.string}")
            print()
        
        # Network hidden nodes
        print(f"    HIDDEN NODES ({len(network.hiddens)}):")
        if len(network.hiddens) == 0:
            print("      No hidden nodes")
        else:
            for j, hidden in enumerate(network.hiddens):
                print(f"      Hidden {j}: {type(hidden)}")
                print(f"        String: {hidden}")
                if hasattr(hidden, 'variable_name'):
                    print(f"        Variable name: {hidden.variable_name}")
        print()
        
        # Network outputs
        print(f"    OUTPUTS ({len(network.outputs)}):")
        for j, output in enumerate(network.outputs):
            print(f"      Output {j}: {type(output)}")
            print(f"        String: {output}")
            if hasattr(output, 'variable_name'):
                print(f"        Variable name: {output.variable_name}")
            if hasattr(output, 'elementtype'):
                print(f"        Element type: {output.elementtype}")
            if hasattr(output, 'tensorshape'):
                print(f"        Tensor shape: {output.tensorshape}")
            if hasattr(output, 'string'):
                print(f"        String field: {output.string}")
            print()
    
    # Iterate over assertions
    print("ASSERTIONS:")
    for i, assertion in enumerate(query.assertions):
        print(f"  Assertion {i}: {type(assertion)}")
        print(f"    String representation: {assertion}")
        print(f"    Pretty string: {vnnlib.node_to_pretty_string(assertion)}")
        
        # Try to access assertion details if available
        if hasattr(assertion, 'expr'):
            print(f"    Expression: {type(assertion.expr).__name__}")
            
            # Recursively explore the boolean expression tree
            def explore_expr(expr, indent="      "):
                print(f"{indent}Expression: {type(expr).__name__}")
                print(f"{indent}String: {expr}")
                
                # Check all possible attributes dynamically
                attrs_to_check = []
                for attr_name in dir(expr):
                    if not attr_name.startswith('_') and not callable(getattr(expr, attr_name)):
                        try:
                            attr_value = getattr(expr, attr_name)
                            if attr_value is not None:
                                attrs_to_check.append((attr_name, attr_value))
                        except:
                            pass
                
                for attr_name, attr_value in attrs_to_check:
                    if hasattr(attr_value, '__iter__') and not isinstance(attr_value, str) and hasattr(attr_value, '__len__'):
                        # It's a list-like object
                        if len(attr_value) > 0:
                            print(f"{indent}{attr_name}: [{len(attr_value)} items]")
                            for j, item in enumerate(attr_value):
                                if hasattr(item, '__class__') and 'vnnlib' in str(type(item)):
                                    print(f"{indent}  [{j}]:")
                                    explore_expr(item, indent + "    ")
                                else:
                                    print(f"{indent}  [{j}]: {item} ({type(item).__name__})")
                        else:
                            print(f"{indent}{attr_name}: [empty]")
                    elif hasattr(attr_value, '__class__') and 'vnnlib' in str(type(attr_value)):
                        # It's another AST node
                        print(f"{indent}{attr_name}:")
                        explore_expr(attr_value, indent + "  ")
                    else:
                        # It's a simple value
                        print(f"{indent}{attr_name}: {attr_value}")

            explore_expr(assertion.expr)
        print()
    
    print("=" * 60)
    print("Analysis complete!")
    
except Exception as e:
    print(f"Error: {e}")
    import traceback
    traceback.print_exc()

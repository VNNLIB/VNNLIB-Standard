import vnnlib
import os


vnnlib_content = """
(declare-network acc
	(declare-input X Real [3])
	(declare-output Y Real [])
)


(assert (<= (* -1.0 X[0]) 0.0))
(assert (<= X[0] 50.0))
(assert (<= (* -1.0 X[1]) 50.0))
(assert (<= X[1] 50.0))
(assert (<= (* -1.0 X[2]) 0.0))
(assert (<= X[2] 150.0))
(assert (<= (+ (* -1.5 X[1]) X[2]) -15.0))

(assert (or 
	(<= Y[0] -3.0)
	(>= Y[0] 0.0)
))
"""

vnnlib_file_path = "example.vnnlib"
with open(vnnlib_file_path, "w") as f:
    f.write(vnnlib_content)

print(f"Attempting to parse: {vnnlib_file_path}\n")

try:
    # 1. Parse the VNNLib file
    query_ast = vnnlib.parse_vnnlib(vnnlib_file_path)
    print("Successfully parsed VNNLib file!")
    print(f"Query Object Type: {type(query_ast)}")
    print(f"Query AST as string:\n{str(query_ast)}\n") 

    # 2. Traverse Network Definitions
    print("--- Networks ---")
    for network_def in query_ast.networks:
        print(f"  Network Definition Type: {type(network_def)}")
        print(f"  Network Variable Name: {network_def.variable_name}")
        print(f"  Network as string: {str(network_def)}")

        # Traverse Input Definitions for this network
        print("    Inputs:")
        for input_def in network_def.inputs :
            print(f"      Input Variable: {input_def.variable_name}") 
            print(f"        Type: {str(input_def.element_type)}") 
            print(f"        Type Object: {type(input_def.element_type)}")
            # Traverse shape (ListInt)
            shape_str = []
            for i in input_def.shape.dims:
                shape_str.append(i) 
            print(f"        Shape: ({', '.join(shape_str)})")

        # Traverse Output Definitions (similar to inputs)
        print("    Outputs:")
        for output_def in network_def.outputs:
            print(f"      Output Variable: {output_def.variable_name}")
            print(f"        Type: {str(output_def.element_type)}")
            # Traverse shape
            shape_str = []
            current_shape_node = output_def.shape
            for i in input_def.shape.dims:
                shape_str.append(i) 
            print(f"        Shape: ({', '.join(shape_str)})")
        
    # 3. Traverse Assertions
    print("\n--- Assertions ---")
    assert_count = 0
    for assertion_item in query_ast.assertions:
        assert_count += 1
        print(f"  assertion {assert_count} Type: {type(assertion_item)}")
        print(f"  assertion as string: {str(assertion_item)}")

        bool_expr = assertion_item.expr # assert::boolexpr_
        if bool_expr:
            print(f"    Boolean Expr Type: {type(bool_expr)}") 
            print(f"    Boolean Expr as string: {str(bool_expr)}")


            if isinstance(bool_expr, vnnlib.GreaterEqual): 
                print(f"      LHS (expr1): {str(bool_expr.expr1)} (Type: {type(bool_expr.expr1)})")
                # bool_expr.expr1 should be an ArithExpr, e.g., VarExpr
                if isinstance(bool_expr.expr1, vnnlib.VarExpr):
                        print(f"        VarExpr Tensor Element: {bool_expr.expr1.tensor_element}")
                
                print(f"      RHS (expr2): {str(bool_expr.expr2)} (Type: {type(bool_expr.expr2)})")
                # bool_expr.expr2 should be an ArithExpr, e.g., DoubleExpr
                if isinstance(bool_expr.expr2, vnnlib.DoubleExpr):
                    print(f"        DoubleExpr Value: {bool_expr.expr2.current}")
            
            elif isinstance(bool_expr, vnnlib.LessThan):
                print(f"      LHS (expr1): {str(bool_expr.expr1)} (Type: {type(bool_expr.expr1)})")
                print(f"      RHS (expr2): {str(bool_expr.expr2)} (Type: {type(bool_expr.expr2)})")

except RuntimeError as e:
    print(f"An error occurred: {e}")
except ImportError:
    print("Failed to import the 'vnnlib' module. Ensure it's built and in PYTHONPATH.")
finally:
    # Clean up the dummy file
    if os.path.exists(vnnlib_file_path):
        os.remove(vnnlib_file_path)






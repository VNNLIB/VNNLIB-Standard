"""
Unit tests for CompatTransformer (reachability format conversion) functionality.
"""

import pytest
import vnnlib
import vnnlib.compat
from typing import List, Tuple
import math


class TestCompatTransformer:
    """Test class for CompatTransformer reachability format conversion."""

    def _parse_and_transform(self, vnnlib_content: str) -> List[vnnlib.compat.SpecCase]:
        """Helper method to parse VNNLIB content and transform to reachability format."""
        query = vnnlib.parse_vnnlib_str(vnnlib_content)
        return vnnlib.compat.transform(query)

    def _assert_box_bounds(self, input_box: List[Tuple[float, float]], expected_bounds: List[Tuple[float, float]]):
        """Assert that input box matches expected bounds (with inf handling)."""
        assert len(input_box) == len(expected_bounds), f"Expected {len(expected_bounds)} dimensions, got {len(input_box)}"
        
        for i, ((actual_lower, actual_upper), (expected_lower, expected_upper)) in enumerate(zip(input_box, expected_bounds)):
            # Handle infinite bounds
            if math.isinf(expected_lower):
                assert math.isinf(actual_lower) and actual_lower < 0, f"Expected -inf for dimension {i}, got {actual_lower}"
            else:
                assert abs(actual_lower - expected_lower) < 1e-9, f"Lower bound mismatch for dimension {i}: expected {expected_lower}, got {actual_lower}"
            
            if math.isinf(expected_upper):
                assert math.isinf(actual_upper) and actual_upper > 0, f"Expected +inf for dimension {i}, got {actual_upper}"
            else:
                assert abs(actual_upper - expected_upper) < 1e-9, f"Upper bound mismatch for dimension {i}: expected {expected_upper}, got {actual_upper}"

    def _assert_polytope_constraints(self, polytope: vnnlib.compat.Polytope, expected_constraints: List[Tuple[List[float], float]]):
        """Assert that polytope constraints match expected format."""
        assert len(polytope.coeff_matrix) == len(expected_constraints), f"Expected {len(expected_constraints)} constraints, got {len(polytope.coeff_matrix)}"
        assert len(polytope.rhs) == len(expected_constraints), f"RHS size mismatch"
        
        for i, ((expected_coeffs, expected_rhs), actual_coeffs, actual_rhs) in enumerate(zip(expected_constraints, polytope.coeff_matrix, polytope.rhs)):
            assert len(actual_coeffs) == len(expected_coeffs), f"Coefficient vector size mismatch for constraint {i}"
            
            for j, (actual_coeff, expected_coeff) in enumerate(zip(actual_coeffs, expected_coeffs)):
                assert abs(actual_coeff - expected_coeff) < 1e-9, f"Coefficient mismatch at [{i}, {j}]: expected {expected_coeff}, got {actual_coeff}"
            
            assert abs(actual_rhs - expected_rhs) < 1e-9, f"RHS mismatch for constraint {i}: expected {expected_rhs}, got {actual_rhs}"

    def test_basic_input_output_constraints(self):
        """Test basic input and output constraints without disjunctions."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (<= X[0] 1.0))
        (assert (>= X[0] 0.0))
        (assert (<= Y[0] 2.0))
        """
        
        cases = self._parse_and_transform(content)
        assert len(cases) == 1, "Expected 1 base case for no disjunctions"

    def test_single_output_disjunction(self):
        """Test specification with a single output disjunction."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [2])
        )
        (assert (<= X[0] 1.0))
        (assert (>= X[0] 0.0))
        (assert (or (<= Y[0] 2.0) (<= Y[1] 3.0)))
        """
        cases = self._parse_and_transform(content)
        assert len(cases) == 1, "Expected 1 specification case"
        case = cases[0]

        # Check input bounds: X[0] ∈ [0, 1], X[1] ∈ [-inf, inf]
        self._assert_box_bounds(case.input_box, [(0.0, 1.0), (-float('inf'), float('inf'))])
        
        # Check output constraints: 2 polytopes (one for each disjunct)
        assert len(case.output_constraints) == 2, "Expected 2 polytopes in disjunction"
        
        # First polytope: Y[0] <= 2.0 (coeffs: [1, 0], rhs: 2.0)
        self._assert_polytope_constraints(case.output_constraints[0], [([1.0, 0.0], 2.0)])
        
        # Second polytope: Y[1] <= 3.0 (coeffs: [0, 1], rhs: 3.0)
        self._assert_polytope_constraints(case.output_constraints[1], [([0.0, 1.0], 3.0)])

    def test_conjunction_of_output_constraints(self):
        """Test specification with conjunction of output constraints."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [2])
        )
        (assert (or (and (<= Y[0] 2.0) (<= Y[1] 3.0)) (<= Y[0] 1.0)))
        """
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1, "Expected 1 specification case"
        case = cases[0]
        
        # Check input bounds: X[0] ∈ [-inf, inf]
        self._assert_box_bounds(case.input_box, [(-float('inf'), float('inf'))])
        
        # Check output constraints: 2 polytopes
        assert len(case.output_constraints) == 2, "Expected 2 polytopes in disjunction"
        
        # First polytope: (Y[0] <= 2.0) AND (Y[1] <= 3.0)
        self._assert_polytope_constraints(case.output_constraints[0], [
            ([1.0, 0.0], 2.0),  # Y[0] <= 2.0
            ([0.0, 1.0], 3.0)   # Y[1] <= 3.0
        ])
        
        # Second polytope: Y[0] <= 1.0
        self._assert_polytope_constraints(case.output_constraints[1], [([1.0, 0.0], 1.0)])

    def test_complex_nested_disjunction(self):
        """Test specification with nested disjunctions and conjunctions."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [2])
        )
        (assert (or (and (<= Y[0] 1.0) (<= Y[1] 2.0)) 
                    (and (<= Y[0] 3.0) (<= Y[1] 4.0))))
        """
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1, "Expected 1 specification case"
        case = cases[0]
        
        # Check output constraints: 2 polytopes
        assert len(case.output_constraints) == 2, "Expected 2 polytopes"
        
        # First polytope: (Y[0] <= 1.0) AND (Y[1] <= 2.0)
        self._assert_polytope_constraints(case.output_constraints[0], [
            ([1.0, 0.0], 1.0),  # Y[0] <= 1.0
            ([0.0, 1.0], 2.0)   # Y[1] <= 2.0
        ])
        
        # Second polytope: (Y[0] <= 3.0) AND (Y[1] <= 4.0)
        self._assert_polytope_constraints(case.output_constraints[1], [
            ([1.0, 0.0], 3.0),  # Y[0] <= 3.0
            ([0.0, 1.0], 4.0)   # Y[1] <= 4.0
        ])

    def test_input_bounds_with_inequalities(self):
        """Test various input bound constraints."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (<= X[0] 5.0))
        (assert (>= X[0] -2.0))
        (assert (<= X[1] 10.0))
        (assert (>= X[2] 0.0))
        (assert (or (<= Y[0] 1.0)))
        """
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1, "Expected 1 specification case"
        case = cases[0]
        
        # Check input bounds
        self._assert_box_bounds(case.input_box, [
            (-2.0, 5.0),                           # X[0]: [-2.0, 5.0]
            (-float('inf'), 10.0),                 # X[1]: [-inf, 10.0]
            (0.0, float('inf'))                    # X[2]: [0.0, inf]
        ])

    def test_greater_equal_constraints(self):
        """Test >= constraints are properly converted to <= form."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [2])
        )
        (assert (or (>= Y[0] -1.0) (>= Y[1] -2.0)))
        """
        cases = self._parse_and_transform(content)

        assert len(cases) == 1
        case = cases[0]

        assert len(case.output_constraints) == 2

        # First polytope: Y[0] >= -1.0 → -Y[0] <= 1.0 (coeffs: [-1, 0], rhs: 1.0)
        self._assert_polytope_constraints(case.output_constraints[0], [([-1.0, 0.0], 1.0)])

        # Second polytope: Y[1] >= -2.0 → -Y[1] <= 2.0 (coeffs: [0, -1], rhs: 2.0)
        self._assert_polytope_constraints(case.output_constraints[1], [([0.0, -1.0], 2.0)])

    def test_multiple_disjunctions(self):
        """Test specification with multiple separate disjunctions."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [2])
        )
        (assert (or (<= Y[0] 1.0) (<= Y[1] 2.0)))
        (assert (or (<= Y[0] 3.0) (<= Y[1] 4.0)))
        """
        cases = self._parse_and_transform(content)
        assert len(cases) == 1, "Expected 1 specification case"
        case = cases[0]

        # Should have 4 polytopes (cartesian product of the two disjunctions)
        # (Y[0] <= 1.0) ∧ (Y[0] <= 3.0), (Y[0] <= 1.0) ∧ (Y[1] <= 4.0), 
        # (Y[1] <= 2.0) ∧ (Y[0] <= 3.0), (Y[1] <= 2.0) ∧ (Y[1] <= 4.0)
        assert len(case.output_constraints) == 4

    def test_mult_network_error(self):
        """Test that multi-network specifications are rejected."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (declare-network net2
            (declare-input Z Real [1])
            (declare-output W Real [1])
        )
        (assert (<= Y[0] 1.0))
        """
        with pytest.raises(vnnlib.VNNLibException, match="Only single-network queries are supported"):
            self._parse_and_transform(content)

    def test_multiple_input_variables_error(self):
        """Test that multiple input variables are rejected."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-input Z Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= Y[0] 1.0))
        """
        with pytest.raises(vnnlib.VNNLibException, match="Multiple input variables found"):
            self._parse_and_transform(content)

    def test_multiple_output_variables_error(self):
        """Test that multiple output variables are rejected."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
            (declare-output Z Real [1])
        )
        (assert (<= Y[0] 1.0))
        """
        with pytest.raises(vnnlib.VNNLibException, match="Multiple output variables found"):
            self._parse_and_transform(content)

    def test_multi_dimensional_input(self):
        """Test with multi-dimensional input arrays."""
        # Note: VNNLib syntax uses separate dimensions, not space-separated 
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [4])
            (declare-output Y Real [1])
        )
        (assert (<= X[0] 1.0))
        (assert (>= X[3] -1.0))
        (assert (or (<= Y[0] 2.0)))
        """
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1
        case = cases[0]
        
        # Should have 4 dimensions for the input
        assert len(case.input_box) == 4
        
        # X[0] <= 1.0 affects index 0, X[3] >= -1.0 affects index 3
        expected_bounds = [
            (-float('inf'), 1.0),           # X[0]
            (-float('inf'), float('inf')),  # X[1]
            (-float('inf'), float('inf')),  # X[2]
            (-1.0, float('inf'))            # X[3]
        ]
        self._assert_box_bounds(case.input_box, expected_bounds)

    def test_arithmetic_expressions_in_constraints(self):
        """Test constraints with arithmetic expressions."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [2])
        )
        (assert (<= (* 2.0 X[0]) 10.0))
        (assert (or (<= (* 2.0 Y[0]) 6.0) (<= (+ Y[0] Y[1]) 9.0)))
        """
        # Test with simple arithmetic expressions (single variable input, multi-variable output)
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1
        case = cases[0]
        
        # Input constraint: 2.0*X[0] <= 10.0 should bound X[0] to (-inf, 5.0]
        expected_bounds = [
            (-float('inf'), 5.0),  # X[0]: 2.0*X[0] <= 10.0 => X[0] <= 5.0
            (-float('inf'), float('inf'))  # X[1]: unbounded
        ]
        self._assert_box_bounds(case.input_box, expected_bounds)
        
        # Output constraints: disjunction with arithmetic expressions
        assert len(case.output_constraints) == 2
        
        # First polytope: 2*Y[0] <= 6.0 (coeffs: [2, 0], rhs: 6.0)
        self._assert_polytope_constraints(case.output_constraints[0], [([2.0, 0.0], 6.0)])
        
        # Second polytope: Y[0] + Y[1] <= 9.0 (coeffs: [1, 1], rhs: 9.0)
        self._assert_polytope_constraints(case.output_constraints[1], [([1.0, 1.0], 9.0)])

    def test_edge_case_single_constraint_disjunction(self):
        """Test edge case with single constraint in disjunction."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (or (<= Y[0] 5.0)))
        """
        
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1
        case = cases[0]
        
        assert len(case.output_constraints) == 1
        self._assert_polytope_constraints(case.output_constraints[0], [([1.0], 5.0)])

    def test_mixed_input_output_constraints_error(self):
        """Test that mixed input-output constraints are rejected."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (or (<= (+ X[0] Y[0]) 5.0)))
        """
        
        # Mixed input-output constraints should be rejected
        with pytest.raises(vnnlib.VNNLibException, match="Input-output mixed constraints are not supported"):
            self._parse_and_transform(content)

    def test_large_disjunction(self):
        """Test specification with a larger disjunction."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [3])
        )
        (assert (or (<= Y[0] 1.0) (<= Y[1] 2.0) (<= Y[2] 3.0) (>= Y[0] -1.0)))
        """
        
        cases = self._parse_and_transform(content)
        
        assert len(cases) == 1
        case = cases[0]
        
        # Should have 4 polytopes (one for each disjunct)
        assert len(case.output_constraints) == 4
        
        # Check each polytope
        self._assert_polytope_constraints(case.output_constraints[0], [([1.0, 0.0, 0.0], 1.0)])  # Y[0] <= 1.0
        self._assert_polytope_constraints(case.output_constraints[1], [([0.0, 1.0, 0.0], 2.0)])  # Y[1] <= 2.0
        self._assert_polytope_constraints(case.output_constraints[2], [([0.0, 0.0, 1.0], 3.0)])  # Y[2] <= 3.0
        self._assert_polytope_constraints(case.output_constraints[3], [([-1.0, 0.0, 0.0], 1.0)]) # Y[0] >= -1.0
"""
Unit tests for LinearArithExpr linearization functionality.

This module tests the linearize method on various arithmetic expressions,
covering basic operations, complex expressions, edge cases, and error conditions.
"""

import json
import pytest
import vnnlib
from typing import List, Tuple


class TestLinearization:
    """Test class for LinearArithExpr linearization functionality."""

    def _parse_and_get_lhs(self, vnnlib_content: str):
        """Helper method to parse VNNLIB content and extract LHS of first assertion."""
        query = vnnlib.parse_vnnlib_str(vnnlib_content)
        assertion = query.assertions[0]
        comparison = assertion.children()[0]
        lhs = comparison.children()[0]
        return lhs

    def _assert_linear_expr(self, linear_expr, expected_constant: float, expected_terms: List[Tuple[float, str]]):
        """Helper method to assert LinearArithExpr matches expected values."""
        assert abs(linear_expr.constant - expected_constant) < 1e-9, f"Expected constant {expected_constant}, got {linear_expr.constant}"
        
        actual_terms = [(term.coeff, term.var_name) for term in linear_expr.terms]
        expected_terms_sorted = sorted(expected_terms, key=lambda x: x[1])  # Sort by variable name
        actual_terms_sorted = sorted(actual_terms, key=lambda x: x[1])
        
        assert len(actual_terms_sorted) == len(expected_terms_sorted), f"Expected {len(expected_terms_sorted)} terms, got {len(actual_terms_sorted)}"
        
        for (expected_coeff, expected_var), (actual_coeff, actual_var) in zip(expected_terms_sorted, actual_terms_sorted):
            assert abs(actual_coeff - expected_coeff) < 1e-9, f"Expected coefficient {expected_coeff} for {expected_var}, got {actual_coeff}"
            assert actual_var == expected_var, f"Expected variable {expected_var}, got {actual_var}"

    # Basic Operations Test (Single Variable) ----------------------------------------------------------------------------------------------------

    def test_single_variable(self):
        """Test linearization of a simple variable."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= X[0] 10.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(1.0, "X[0]")])

    def test_single_constant(self):
        """Test linearization of a constant."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= 5.0 10.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 5.0, [])

    def test_flat_addition(self):
        """Test linearization of variable + constant."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (+ X[0] 5.0) 10.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 5.0, [(1.0, "X[0]")])

    def test_variable_constant_subtraction(self):
        """Test linearization of variable - constant."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (- X[0] 5.0) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, -5.0, [(1.0, "X[0]")])

    def test_constant_variable_subtraction(self):
        """Test linearization of constant - variable."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (- 5.0 X[0]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 5.0, [(-1.0, "X[0]")])

    def test_variable_constant_multiplication(self):
        """Test linearization of variable * constant."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* X[0] 3.5) 7.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(3.5, "X[0]")])

    def test_constant_variable_multiplication(self):
        """Test linearization of constant * variable."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* -2.0 X[0]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(-2.0, "X[0]")])

    def test_flat_negation(self):
        """Test linearization of negated variable."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (- X[0]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(-1.0, "X[0]")])

    def test_negative_coefficients(self):
        """Test linearization with negative coefficients."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* -5.0 X[0]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(-5.0, "X[0]")])

    # Multiple Variable Tests (Same and Different) --------------------------------------------------------------------------------------------------------------

    def test_two_same_variables(self):
        """Test linearization of expression with same variable multiple times."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (<= (+ X[0] 5.0 X[0]) 10.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 5.0, [(2.0, "X[0]")])

    def test_variable_cancellation(self):
        """Test linearization where variables cancel out."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (- X[0] X[0]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [])

    def test_two_different_variables(self):
        """Test linearization with two different variables."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (<= (+ (- X[0] X[1]) 3.0) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 3.0, [(1.0, "X[0]"), (-1.0, "X[1]")])

    def test_three_different_variables(self):
        """Test linearization with three different variables."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (<= (- X[0] X[1] X[2]) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(1.0, "X[0]"), (-1.0, "X[1]"), (-1.0, "X[2]")])

    # Complex Expression Tests ----------------------------------------------------------------------------------------------------------------------------------

    def test_mixed_operations(self):
        """Test linearization of complex nested expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (<= (+ 5.0 (* -1.0 X[0]) (- X[1])) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 5.0, [(-1.0, "X[0]"), (-1.0, "X[1]")])

    def test_nested_multiplication(self):
        """Test linearization of nested multiplication with constants."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (+ (* 2.0 (* X[0] 3.0)) 2.0) 20.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 2.0, [(6.0, "X[0]")])

    # Zero Coefficient and Identity Tests --------------------------------------------------------------------------------------------------------------------

    def test_multiplication_by_zero(self):
        """Test linearization of variable * 0."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* X[0] 0.0) 0.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [])

    def test_multiplication_by_one(self):
        """Test linearization of variable * 1."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* X[0] 1.0) 5.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(1.0, "X[0]")])

    def test_addition_with_zero(self):
        """Test linearization of variable + 0."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (+ X[0] 0.0) 5.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(1.0, "X[0]")])

    # Pure Constants Tests ----------------------------------------------------------------------------------------------------------------------------------------

    def test_constant_multiplication(self):
        """Test linearization of pure constant multiplication."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* 2.0 3.0 2.5) 20.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 15.0, [])

    def test_constant_addition(self):
        """Test linearization of pure constant addition."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (+ 1.0 2.0 5.0) 10.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 8.0, [])

    # Edge Case Tests --------------------------------------------------------------------------------------------------------------------------------------------

    def test_small_coefficients(self):
        """Test linearization with small coefficients."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* 0.0001 X[0]) 0.1))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(0.0001, "X[0]")])

    def test_large_coefficients(self):
        """Test linearization with large coefficients."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= (* 1000000.0 X[0]) 1000.0))
        """
        lhs = self._parse_and_get_lhs(content)
        linear = lhs.linearize()
        self._assert_linear_expr(linear, 0.0, [(1000000.0, "X[0]")])

    # Non-linear Error Tests ---------------------------------------------------------------------------------------------------------------------------------------

    def test_nonlinear_expression_should_fail(self):
        """Test that complex non-linear expressions raise exceptions."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (<= (* X[0] (+ X[1] 2.0)) 25.0))
        """
        lhs = self._parse_and_get_lhs(content)
        with pytest.raises(Exception) as exc_info:
            lhs.linearize()
        
        assert "non-linear" in str(exc_info.value).lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
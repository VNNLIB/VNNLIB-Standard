"""
Unit tests for DNF (Disjunctive Normal Form) conversion functionality.
"""

import json
import pytest
import vnnlib
from typing import List, Set, Tuple


class TestDNFConversion:
    """Test class for Boolean expression DNF conversion functionality."""

    def _parse_and_get_bool_expr(self, vnnlib_content: str):
        """Helper method to parse VNNLIB content and extract Boolean expression from first assertion."""
        query = vnnlib.parse_vnnlib_str(vnnlib_content)
        assertion = query.assertions[0]
        return assertion.expr

    def _assert_dnf_structure(self, dnf, expected_clause_count: int, expected_clause_sizes: List[int]):
        """Helper method to assert DNF structure matches expectations."""
        assert len(dnf) == expected_clause_count, f"Expected {expected_clause_count} clauses, got {len(dnf)}"
        
        actual_sizes = [len(clause) for clause in dnf]
        expected_sizes = sorted(expected_clause_sizes)
        actual_sizes_sorted = sorted(actual_sizes)
        
        assert actual_sizes_sorted == expected_sizes, f"Expected clause sizes {expected_sizes}, got {actual_sizes_sorted}"

    def _get_literal_signature(self, literal):
        """Get a string signature for a literal for comparison."""
        lhs_str = str(literal.lhs)
        rhs_str = str(literal.rhs)
        op_name = type(literal).__name__
        return f"{op_name}({lhs_str}, {rhs_str})"

    def _assert_clause_contains_literals(self, clause, expected_literal_patterns: List[str]):
        """Assert that a clause contains literals matching expected patterns."""
        actual_signatures = [self._get_literal_signature(lit) for lit in clause]
        
        for pattern in expected_literal_patterns:
            found = any(pattern in sig for sig in actual_signatures)
            assert found, f"Expected pattern '{pattern}' not found in clause. Actual: {actual_signatures}"

    # Basic DNF Tests - Single Literals ----------------------------------------

    def test_single_comparison(self):
        """Test DNF of a single comparison expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [1])
            (declare-output Y Real [1])
        )
        (assert (<= X[0] 10.0))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        self._assert_dnf_structure(dnf, 1, [1])
        self._assert_clause_contains_literals(dnf[0], ["LessEqual"])

    # Conjunction Tests --------------------------------------------------------

    def test_simple_conjunction(self):
        """Test DNF of a simple AND expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (and (<= X[0] 10.0) (>= X[1] 5.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        # AND in DNF: single clause with multiple literals
        self._assert_dnf_structure(dnf, 1, [2])
        self._assert_clause_contains_literals(dnf[0], ["LessEqual", "GreaterEqual"])

    def test_three_way_conjunction(self):
        """Test DNF of a three-way AND expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (and (<= X[0] 10.0) (>= X[1] 5.0) (<= X[2] 20.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        self._assert_dnf_structure(dnf, 1, [3])
        self._assert_clause_contains_literals(dnf[0], ["LessEqual", "GreaterEqual", "LessEqual"])

    # Disjunction Tests --------------------------------------------------------

    def test_simple_disjunction(self):
        """Test DNF of a simple OR expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (or (<= X[0] 10.0) (>= X[1] 5.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        # OR in DNF: multiple clauses with single literals
        self._assert_dnf_structure(dnf, 2, [1, 1])

    def test_three_way_disjunction(self):
        """Test DNF of a three-way OR expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (or (<= X[0] 10.0) (>= X[1] 5.0) (<= X[2] 0.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        self._assert_dnf_structure(dnf, 3, [1, 1, 1])

    # Distributive Law Tests ---------------------------------------------------

    def test_and_of_ors(self):
        """Test DNF distribution with three OR clauses: (A OR B) AND (C OR D) AND (E OR F)"""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [3])
            (declare-output Y Real [3])
        )
        (assert (and (or (<= X[0] 10.0) (>= X[1] 5.0)) 
                     (or (<= X[2] 20.0) (>= Y[0] 15.0))
                     (or (<= Y[1] 30.0) (>= Y[2] 25.0))))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        # Should distribute to 8 clauses (2×2×2), each with 3 literals
        self._assert_dnf_structure(dnf, 8, [3, 3, 3, 3, 3, 3, 3, 3])

    # Complex Nested Expressions -----------------------------------------------

    def test_nested_expression(self):
        """Test DNF of a deeply nested expression."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [4])
            (declare-output Y Real [2])
        )
        (assert (and (or (<= X[0] 10.0) (and (>= X[1] 5.0) (<= X[2] 15.0))) 
                     (or (>= Y[0] 20.0) (<= Y[1] 25.0))))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        self._assert_dnf_structure(dnf, 4, [2, 2, 3, 3])

    # Reference Preservation Tests ---------------------------------------------

    def test_reference_preservation(self):
        """Test that DNF literals maintain references to original AST nodes."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (or (<= X[0] 10.0) (>= X[1] 5.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        # Check that literals are proper Compare objects with valid LHS/RHS
        for clause in dnf:
            for literal in clause:
                assert hasattr(literal, 'lhs'), "Literal should have LHS"
                assert hasattr(literal, 'rhs'), "Literal should have RHS"
                assert literal.lhs is not None, "LHS should not be None"
                assert literal.rhs is not None, "RHS should not be None"

    def test_complex_arithmetic(self):
        """Test DNF with complex arithmetic expressions in comparisons."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network test
            (declare-input X Real [2])
            (declare-output Y Real [1])
        )
        (assert (and (<= (+ X[0] X[1]) 10.0) (>= (* -1.0 X[0]) -5.0)))
        """
        bool_expr = self._parse_and_get_bool_expr(content)
        dnf = bool_expr.dnf_form()
        
        self._assert_dnf_structure(dnf, 1, [2])


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

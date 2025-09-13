"""
Unit tests for DNF (Disjunctive Normal Form) conversion functionality.
"""

import json
import pytest
import vnnlib
from typing import List, Set, Tuple
from vnnlib import BoolExpr


class TestDNFConversion:
    """Test class for Boolean expression DNF conversion functionality."""

    def _parse_and_get_bool_expr(self, vnnlib_content: str):
        """Helper method to parse VNNLIB content and extract Boolean expression from first assertion."""
        query = vnnlib.parse_vnnlib_str(vnnlib_content)
        assertion = query.assertions[0]
        return assertion.expr

    def _assert_dnf_equals(self, dnf: List[Set[BoolExpr]], expected_dnf: List[Set[str]]):
        """Assert that the DNF matches the expected stringified DNF"""
        assert len(dnf) == len(expected_dnf), f"Expected {len(expected_dnf)} clauses, got {len(dnf)}"
        
        for clause, expected_lits in zip(dnf, expected_dnf):
            assert len(clause) == len(expected_lits), f"Expected clause size {len(expected_lits)}, got {len(clause)}"

            actual_lits = {str(lit) for lit in clause}
            assert actual_lits == expected_lits, f"Expected literals {expected_lits}, got {actual_lits}"

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
        
        self._assert_dnf_equals(dnf, [{"(<= X [0] 10.0) "}])

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
        self._assert_dnf_equals(dnf, [{"(<= X [0] 10.0) ", "(>= X [1] 5.0) "}])

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
        
        self._assert_dnf_equals(dnf, [{"(<= X [0] 10.0) ", "(>= X [1] 5.0) ", "(<= X [2] 20.0) "}])

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
        self._assert_dnf_equals(dnf, [{"(<= X [0] 10.0) "}, {"(>= X [1] 5.0) "}])

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
        
        self._assert_dnf_equals(dnf, [{"(<= X [0] 10.0) "}, {"(>= X [1] 5.0) "}, {"(<= X [2] 0.0) "}])

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
        self._assert_dnf_equals(dnf, [
            {"(<= X [0] 10.0) ", "(<= X [2] 20.0) ", "(<= Y [1] 30.0) "},
            {"(<= X [0] 10.0) ", "(<= X [2] 20.0) ", "(>= Y [2] 25.0) "},
            {"(<= X [0] 10.0) ", "(>= Y [0] 15.0) ", "(<= Y [1] 30.0) "},
            {"(<= X [0] 10.0) ", "(>= Y [0] 15.0) ", "(>= Y [2] 25.0) "},
            {"(>= X [1] 5.0) ", "(<= X [2] 20.0) ", "(<= Y [1] 30.0) "},
            {"(>= X [1] 5.0) ", "(<= X [2] 20.0) ", "(>= Y [2] 25.0) "},
            {"(>= X [1] 5.0) ", "(>= Y [0] 15.0) ", "(<= Y [1] 30.0) "},
            {"(>= X [1] 5.0) ", "(>= Y [0] 15.0) ", "(>= Y [2] 25.0) "}
        ])

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
        
        self._assert_dnf_equals(dnf, [
            {"(<= X [0] 10.0) ", "(>= Y [0] 20.0) "},
            {"(<= X [0] 10.0) ", "(<= Y [1] 25.0) "},
            {"(>= X [1] 5.0) ", "(<= X [2] 15.0) ", "(>= Y [0] 20.0) "},
            {"(>= X [1] 5.0) ", "(<= X [2] 15.0) ", "(<= Y [1] 25.0) "}
        ])

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
        
        self._assert_dnf_equals(dnf, [{"(<= (+ X [0] X [1]) 10.0) ", "(>= (* -1.0 X [0]) -5.0) "}])


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

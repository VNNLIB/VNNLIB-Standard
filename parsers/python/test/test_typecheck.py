"""
Unit tests for type checking functionality.

This module tests the type checker's ability to detect and report
various type mismatches between variables and constants, mixed types,
and precision compatibility issues.
"""

import json
import pytest
import vnnlib
from typing import Dict, Any, Set


class TestTypeChecker:
    """Test class for type checking functionality."""

    def _assert_error_count(self, exc_info, expected_count: int):
        """Helper method to assert error count in VNNLibException."""
        json_error = json.loads(str(exc_info.value))
        assert len(json_error["errors"]) == expected_count, f"Expected {expected_count} errors, got {len(json_error['errors'])}"
        return json_error

    def _assert_error_contains(self, json_error: Dict[str, Any], error_code: str, symbol: str, error_index: int = 0):
        """Helper method to assert error contains specific code and symbol."""
        errors = json_error["errors"]
        assert error_code in errors[error_index]["errorCode"], f"Expected error code containing '{error_code}', got '{errors[error_index]['errorCode']}'"
        assert errors[error_index]["offendingSymbol"] == symbol, f"Expected offending symbol '{symbol}', got '{errors[error_index]['offendingSymbol']}'"

    def _assert_type_mismatch_errors(self, json_error: Dict[str, Any], expected_symbols: Set[str]):
        """Helper method to assert all errors are type mismatches with expected symbols."""
        actual_symbols = set()
        for error in json_error["errors"]:
            assert "TypeMismatch" in error["errorCode"]
            actual_symbols.add(error["offendingSymbol"])
        assert actual_symbols == expected_symbols

    # Variable-Constant Type Mismatch Tests -----------------------------------------------------------------------------------------------------------------

    def test_float_variable_with_int_constant(self):
        """
        Tests that an expression with a Real variable to an integer constant raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X float16 [1])
            (declare-output Y float16 [1])
        )
        (assert (<= Y[0] 5))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "5")

    def test_int_variable_with_float_constant(self):
        """
        Tests that an expression with an int32 variable to a float constant raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int32 [1])
            (declare-output Y int32 [1])
        )
        (assert (<= Y[0] 3.14))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "3.14")

    def test_uint_variable_with_negative_constant(self):
        """
        Tests that an expression with an unsigned integer variable to a negative constant raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X uint32 [1])
            (declare-output Y uint32 [1])
        )
        (assert (<= Y[0] -5))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "-5")

    # Variable-Variable Type Mismatch Tests -----------------------------------------------------------------------------------------------------------------

    def test_mixed_variable_types(self):
        """
        Tests that an expression with variables of different types (float16 and int32) raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X float16 [1])
            (declare-hidden Z int32 [1] "z_in")
            (declare-output Y float16 [1])
        )
        (assert (<= X[0] Z[0]))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "Z")

    def test_mixed_variable_precision(self):
        """
        Tests that an expression with variables of different precisions (float16 and float32) raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X float16 [1])
            (declare-hidden Z float32 [1] "z_in")
            (declare-output Y float16 [1])
        )
        (assert (<= X[0] Z[0]))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "Z")

    # Constant-Constant Type Mismatch Tests -----------------------------------------------------------------------------------------------------------------

    def test_mixed_constant_types(self):
        """
        Tests that an expression with a float constant and an int constant raises a TypeMismatch error.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int8 [1])
            (declare-output Y int8 [1])
        )
        (assert (<= X[0] (+ 3 3.0)))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TypeMismatch", "3.0")

    # Multiple Error Tests  --------------------------------------------------------------------------------------------------------------------------------

    def test_multiple_operand_mismatches(self):
        """
        Tests that all operand mismatches are reported when multiple mismatches occur in a single operation.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int8 [1])
            (declare-input Z int16 [1])
            (declare-output Y int32 [1])
        )
        (assert (<= 0 (+ X[0] Z[0] 3.14)))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 2)
        
        # Should report both Z (int16 vs int8) and 3.14 (float vs int) mismatches
        self._assert_type_mismatch_errors(json_error, {"Z", "3.14"})

    def test_multiple_assertions_mismatches(self):
        """
        Tests that each assertion with mismatched types is reported separately.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int8 [1])
            (declare-input Z int16 [1])
            (declare-output Y int32 [1])
        )
        (assert (<= 0.0 X[0]))
        (assert (<= 0.0 Z[0]))
        (assert (<= 0.0 Y[0]))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 3)

        # Check that all three variables are reported for type mismatches
        self._assert_type_mismatch_errors(json_error, {"X", "Z", "Y"})

    # Valid Type Combinations Tests --------------------------------------------------------------------------------------------------------------------------

    def test_mismatches_in_connective(self):
        """
        Tests that mismatches between expressions connected by logical operators (and, or)
        are ignored - each expression is checked independently.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int8 [1])
            (declare-input Z int16 [1])
            (declare-output Y int32 [1])
        )
        (assert (and (<= 0 X[0]) (<= 0 Z[0]) (<= 0 Y[0])))
        """
        vnnlib.parse_vnnlib_str(invalid_content)  # No error expected here

    def test_same_type_variables(self):
        """Test that variables of the same type can be used together without errors."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X float32 [1])
            (declare-input Z float32 [1])
            (declare-output Y float32 [1])
        )
        (assert (<= (+ X[0] Z[0]) Y[0]))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    def test_same_precision_integers(self):
        """Test that integers of the same precision can be used together."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int32 [1])
            (declare-input Z int32 [1])
            (declare-output Y int32 [1])
        )
        (assert (<= (+ X[0] Z[0] 42) Y[0]))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    def test_float_with_float_constant(self):
        """Test that float variables work correctly with float constants."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X float32 [1])
            (declare-output Y float32 [1])
        )
        (assert (<= (+ X[0] 3.14) Y[0]))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    def test_int_with_int_constant(self):
        """Test that integer variables work correctly with integer constants."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X int16 [1])
            (declare-output Y int16 [1])
        )
        (assert (<= (+ X[0] 42) Y[0]))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

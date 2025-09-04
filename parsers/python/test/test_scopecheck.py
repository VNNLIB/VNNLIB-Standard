"""
Unit tests for scope checking functionality.

This module tests the scope checker's ability to detect and report
various scoping issues such as duplicate declarations, undeclared variables,
invalid dimensions, and out-of-bounds accesses.
"""

import vnnlib
import pytest
import json
from typing import List, Dict, Any


class TestScopeChecker:
    """Test class for scope checking functionality."""

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

    # Duplicate Declaration Tests ---------------------------------------------------------------------------------------------------------------------------

    def test_duplicate_variable_error(self):
        """
        Tests that declaring the same variable twice raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [3])
            (declare-input X Real [3]) ; Duplicate
            (declare-output Y Real [1])
        )
        (assert (or 
            (<= Y[0] -3.0)
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "MultipleDeclaration", "X")

    # Undeclared Variable Tests -----------------------------------------------------------------------------------------------------------------------

    def test_undeclared_variable_error(self):
        """
        Tests that using an undeclared variable in assertions raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [3])
            (declare-output Y Real [1])
        )
        (assert (or 
            (<= Z[0] -3.0) ; Z is undeclared
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "UndeclaredVariable", "Z")

    # Invalid Dimensions Tests ----------------------------------------------------------------------------------------------------------------------------------

    def test_invalid_dimensions(self):
        """
        Tests that using invalid dimensions (i.e., dimension size of 0) for a variable raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [0, 0])   ; invalid dimensions
            (declare-output Y Real [])
        )
        (assert (or 
            (<= X[10, 10] -3.0) ; out of bounds access
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)
            
        json_error = self._assert_error_count(exc_info, 2)

        # First error should be InvalidDimensions
        self._assert_error_contains(json_error, "InvalidDimensions", "X", 0)
        
        # Second error should be UndeclaredVariable (because variable with invalid dimensions is rejected)
        self._assert_error_contains(json_error, "UndeclaredVariable", "X", 1)

    # Index Bounds Tests ----------------------------------------------------------------------------------------------------------------------------------

    def test_out_of_bounds_indices(self):
        """
        Tests that accessing a scalar variable with an index raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [3, 4])   ; X is a 3x4 matrix
            (declare-output Y Real [])
        )
        (assert (or 
            (<= X[4, 4] -3.0) ; out of bounds access
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        
        self._assert_error_contains(json_error, "IndexOutOfBounds", "X[4,4]")
        # Check that the hint mentions the out of bounds access
        assert "Index 4 is out of bounds" in json_error["errors"][0]["hint"]

    def test_too_many_indices(self):
        """
        Tests that using too many indices on a variable raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [3, 4])   ; X is a 3x4 matrix
            (declare-output Y Real [])
        )
        (assert (or 
            (<= X[1, 2, 3] -3.0) ; too many indices
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "TooManyIndices", "X[1,2,3]")

    def test_not_enough_indices(self):
        """
        Tests that using too few indices on a variable raises a VNNLibError.
        """
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [3, 4])   ; X is a 3x4 matrix
            (declare-output Y Real [])
        )
        (assert (or 
            (<= X[1] -3.0) ; not enough indices
            (>= Y[0] 0.0)
        ))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = self._assert_error_count(exc_info, 1)
        self._assert_error_contains(json_error, "NotEnoughIndices", "X[1]")

    # ONNX Name Consistency Tests -----------------------------------------------------------------------------------------------------------------------------

    def test_inconsistent_onnx_names(self):
        """
        Tests that when named input/output variables are mixed with unnamed ones, 
        a VNNLibError is raised.
        """
        
        def check(content, expected_count=1):
            with pytest.raises(vnnlib.VNNLibException) as exc_info:
                vnnlib.parse_vnnlib_str(content)
            json_error = json.loads(str(exc_info.value))
            assert len(json_error["errors"]) == expected_count
            # All errors should be UnexpectedOnnxName
            for error in json_error["errors"]:
                assert "UnexpectedOnnxName" in error["errorCode"]
        
        # Test with mixed ONNX names across inputs (first input is named)
        check("""
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [] "x_in")          
            (declare-input Z Real [])                 
            (declare-output Y Real [] "y_out")          
        )
        (assert (>= Y[0] 0.0))
        """, expected_count=1)

        # Test with mixed ONNX names across inputs (first input is not named) 
        check("""
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [])                  
            (declare-input Z Real [] "z_in")           
            (declare-output Y Real [] "y_out")         
        )
        (assert (>= Y[0] 0.0))
        """, expected_count=2)  # Reports both Z and Y as inconsistent

        # Test with mixed ONNX names across inputs and outputs
        check("""
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [] "x_in")           
            (declare-input Z Real [] "z_in")           
            (declare-output Y Real [])                 
        )
        (assert (>= Y[0] 0.0))
        """, expected_count=1)  # Only Y is inconsistent

        # Test with multiple named variables, when first input is unnamed (multiple mismatches)
        # The new checker reports all mismatches
        check("""
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [])           
            (declare-input Z Real [] "z_in")       
            (declare-output Y Real [] "y_out")                
        )
        (assert (>= Y[0] 0.0))
        """, expected_count=2)  # Reports both Z and Y as inconsistent

    def test_consistent_onnx_names_all_named(self):
        """Test that all ONNX names is a valid configuration."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [] "x_in")          
            (declare-input Z Real [] "z_in")          
            (declare-output Y Real [] "y_out")          
        )
        (assert (>= Y[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # This should not raise an error

    def test_consistent_onnx_names_none_named(self):
        """Test that no ONNX names is a valid configuration."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network acc
            (declare-input X Real [])           
            (declare-input Z Real [])          
            (declare-output Y Real [])          
        )
        (assert (>= Y[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # This should not raise an error


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
"""
Unit tests for network congruence statements.

This module tests the type checker's ability to validate network congruence
using equal-to and isomorphic-to statements, including ONNX name support,
shape validation, and proper error reporting.

The tests cover:
- Valid congruence cases (equal-to, isomorphic-to)
- ONNX name matching and validation
- Shape and type mismatch detection
- Variable count validation
- Error message accuracy
- Multiple network relationships
"""

import json
import pytest
import vnnlib
from typing import Dict, Any


class TestNetworkCongruenceCheck:
    """Test validation for network congruence statements (isomorphic-to, equal-to)"""

    def _assert_error_count(self, json_error: Dict[str, Any], expected_count: int):
        """Helper method to assert error count in VNNLibException."""
        assert len(json_error["errors"]) == expected_count, f"Expected {expected_count} errors, got {len(json_error['errors'])}"

    def _assert_error_contains(self, json_error: Dict[str, Any], error_substr: str, symbol: str):
        """Helper method to assert error contains specific message substring and symbol."""
        errors = json_error["errors"]
        assert error_substr in errors[0]["message"], f"Expected error message containing '{error_substr}', got '{errors[0]['message']}'"
        assert errors[0]["offendingSymbol"] == symbol, f"Expected offending symbol '{symbol}', got '{errors[0]['offendingSymbol']}'"

    # Valid Congruence Tests ----------------------------------------------------------------

    def test_valid_equal_to_basic(self):
        """Test valid equalTo statement with matching variable shapes."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2])
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    def test_valid_isomorphic_to_basic(self):
        """Test valid isomorphicTo statement with matching variable shapes."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [3])
            (declare-output Y1 Real [2])
        )
        (declare-network net2
            (isomorphic-to net1)
            (declare-input X2 Real [3])
            (declare-output Y2 Real [2])
        )
        (assert (>= X1[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    def test_valid_onnx_congruence(self):
        """Test valid congruence with matching ONNX names."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2] "input_tensor")
            (declare-output Y1 Real [1] "output_tensor")
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2] "input_tensor")
            (declare-output Y2 Real [1] "output_tensor")
        )
        (assert (>= X1[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error

    # Test Congruence Mismatches ------------------------------------------------------------------

    def test_shape_mismatch(self):
        """Test that shape mismatch in input variables is detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2, 3])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [3, 4])
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0, 0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Shape mismatch", "net1")

    def test_variable_count_mismatch(self):
        """Test that different number of variables is detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2])
            (declare-input X3 Real [2])
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Number of variables mismatch", "net1")

    def test_onnx_name_mismatches(self):
        """Test that mismatched ONNX names are detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2] "input_tensor")
            (declare-output Y1 Real [1] "output_tensor")
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2] "different_input")
            (declare-output Y2 Real [1] "output_tensor")
        )
        (assert (>= X1[0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "ONNX name 'different_input' not found", "net1")

    def test_type_mismatches(self):
        """Test that type mismatch in input variables is detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 int32 [2])
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Type mismatch", "net1")

    # ONNX Naming Convention Mismatch ------------------------------------------------------------

    def test_onnx_naming_convention_mismatch(self):
        """Test that ONNX naming convention mismatches are detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2] "input_tensor")
            (declare-output Y1 Real [1] "output_tensor")
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2])  ; Using ordered variables instead of named variables
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Variable naming convention mismatch", "net1")

    # Network Reference Errors -----------------------------------------------------------------

    def test_missing_referenced_network(self):
        """Test that referencing a non-existent network is detected."""
        invalid_content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (equal-to nonexistent)
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(invalid_content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Referenced network 'nonexistent' not found", "nonexistent")

    def test_forward_network_ref(self):
        """Test that forward references to networks are not supported."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (equal-to net2)
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (declare-input X2 Real [2])
            (declare-output Y2 Real [1])
        )
        (assert (>= X1[0] 0.0))
        """
        # Forward references are not supported, so this should fail
        with pytest.raises(vnnlib.VNNLibException) as exc_info:
            vnnlib.parse_vnnlib_str(content)

        json_error = json.loads(str(exc_info.value))
        self._assert_error_count(json_error, 1)
        self._assert_error_contains(json_error, "Referenced network 'net2' not found", "net2")

    # Multiple Network Chain Test ----------------------------------------------------------

    def test_transitive_relationship(self):
        """Test a chain of networks with equalTo relationships."""
        content = """
        (vnnlib-version <2.0>)
        (declare-network net1
            (declare-input X1 Real [2])
            (declare-output Y1 Real [1])
        )
        (declare-network net2
            (equal-to net1)
            (declare-input X2 Real [2])
            (declare-output Y2 Real [1])
        )
        (declare-network net3
            (equal-to net2)
            (declare-input X3 Real [2])
            (declare-output Y3 Real [1])
        )
        
        (assert (>= X1[0] 0.0))
        """
        vnnlib.parse_vnnlib_str(content)  # Should not raise an error


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

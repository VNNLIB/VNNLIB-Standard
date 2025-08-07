import json
import pytest
import vnnlib


def test_float_variable_with_int_constant():
    """
    Tests that an expression with a Real variable to an integer constant raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X float16 [1])
        (declare-output Y float16 [1])
    )
    (assert (<= Y[0] 5))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "5"


def test_int_variable_with_float_constant():
    """
    Tests that an expression with an int32 variable to a float constant raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X int32 [1])
        (declare-output Y int32 [1])
    )
    (assert (<= Y[0] 3.14))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "3.14"


def test_uint_variable_with_negative_constant():
    """
    Tests that an expression with an unsigned integer variable to a negative constant raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X uint32 [1])
        (declare-output Y uint32 [1])
    )
    (assert (<= Y[0] -5))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "-5"


def test_mixed_variable_types():
    """
    Tests that an expression with variables of different types (float16 and int32) raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X float16 [1])
        (declare-hidden Z int32 [1] "z_in")
        (declare-output Y float16 [1])
    )
    (assert (<= X[0] Z[0]))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "Z"


def test_mixed_variable_precision():
    """
    Tests that an expression with variables of different precisions (float16 and float32) raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X float16 [1])
        (declare-hidden Z float32 [1] "z_in")
        (declare-output Y float16 [1])
    )
    (assert (<= X[0] Z[0]))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "Z"


def test_mixed_constant_types():
    """
    Tests that an expression with a float constant and an int constant raises a TypeMismatch error.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X int8 [1])
        (declare-output Y int8 [1])
    )
    (assert (<= X[0] (+ 3 3.0)))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "3.0"


def test_multiple_operand_mismatches():
    """
    Tests that only the first operand mismatch is reported when multiple mismatches occur in a single operation.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X int8 [1])
        (declare-input Z int16 [1])
        (declare-output Y int32 [1])
    )
    (assert (<= 0 (+ X[0] Z[0] 3.14)))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "Z"


def test_multiple_assertions_mismatches():
    """
    Tests that each assertion with mismatched types is reported separately.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X int8 [1])
        (declare-input Z int16 [1])
        (declare-output Y int32 [1])
    )
    (assert (<= 0.0 X[0]))
    (assert (<= 0.0 Z[0]))
    (assert (<= 0.0 Y[0]))
    """
    with pytest.raises(vnnlib.VNNLibError) as exc_info:
        vnnlib.parse_vnnlib_str(invalid_content)

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 3

    assert json_error["errors"][0]["offendingSymbol"] == "X"
    assert "TypeMismatch" in json_error["errors"][2]["errorCode"]

    assert json_error["errors"][1]["offendingSymbol"] == "Z"
    assert "TypeMismatch" in json_error["errors"][0]["errorCode"]

    assert json_error["errors"][2]["offendingSymbol"] == "Y"
    assert "TypeMismatch" in json_error["errors"][1]["errorCode"]


def test_mismatches_in_connective():
    """
    Tests that mismatches between expressions connected by logical operators (and, or)
    are ignored - each expression is checked independently.
    """
    invalid_content = """
    (declare-network acc
        (declare-input X int8 [1])
        (declare-input Z int16 [1])
        (declare-output Y int32 [1])
    )
    (assert (and (<= 0 X[0]) (<= 0 Z[0]) (<= 0 Y[0])))
    """
    vnnlib.parse_vnnlib_str(invalid_content) # No error expected here

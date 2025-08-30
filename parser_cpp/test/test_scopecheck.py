import vnnlib
import pytest
import json


def test_duplicate_variable_error():
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

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "MultipleDeclaration" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "X"


def test_undeclared_variable_error():
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

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    assert "UndeclaredVariable" in json_error["errors"][0]["errorCode"]
    assert json_error["errors"][0]["offendingSymbol"] == "Z"


def test_invalid_dimensions():
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
    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 2

    # First error should be InvalidDimensions
    assert json_error["errors"][0]["offendingSymbol"] == "X"
    assert "InvalidDimensions" in json_error["errors"][0]["errorCode"]
    
    # Second error should be UndeclaredVariable (because variable with invalid dimensions is rejected)
    assert json_error["errors"][1]["offendingSymbol"] == "X"
    assert "UndeclaredVariable" in json_error["errors"][1]["errorCode"]


def test_out_of_bounds_indices():
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

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    
    assert json_error["errors"][0]["offendingSymbol"] == "X[4,4]"
    assert "IndexOutOfBounds" in json_error["errors"][0]["errorCode"]
    # Check that the hint mentions the out of bounds access
    assert "Index 4 is out of bounds" in json_error["errors"][0]["hint"]


def test_too_many_indices():
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

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    
    assert json_error["errors"][0]["offendingSymbol"] == "X[1,2,3]"
    assert "TooManyIndices" in json_error["errors"][0]["errorCode"]


def test_not_enough_indices():
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

    json_error = json.loads(str(exc_info.value))
    assert len(json_error["errors"]) == 1
    
    assert json_error["errors"][0]["offendingSymbol"] == "X[1]"
    assert "NotEnoughIndices" in json_error["errors"][0]["errorCode"]


def test_inconsistent_onnx_names():
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

    # Test with all ONNX names
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

    # Test with no ONNX names
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
        




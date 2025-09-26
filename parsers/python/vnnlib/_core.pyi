"""Type stubs for VNNLib (typed AST)"""

from __future__ import annotations
from typing import List, Tuple, Optional, Any
from enum import Enum

# --- Exceptions --------------------------------------------------------------

class VNNLibException(Exception): ...


# --- Enums / Aliases --------------------------------------------------------

class DType(Enum):
    F16: DType
    F32: DType
    F64: DType
    BF16: DType
    F8E4M3FN: DType
    F8E5M2: DType
    F8E4M3FNUZ: DType
    F8E5M2FNUZ: DType
    F4E2M1: DType
    I8: DType
    I16: DType
    I32: DType
    I64: DType
    U8: DType
    U16: DType
    U32: DType
    U64: DType
    C64: DType
    C128: DType
    Bool: DType
    String: DType
    Unknown: DType
    NegativeIntConstant: DType
    PositiveIntConstant: DType
    FloatConstant: DType

class SymbolKind(Enum):
    Input: SymbolKind
    Hidden: SymbolKind
    Output: SymbolKind
    Unknown: SymbolKind

Shape = List[int]


# --- Base node ---------------------------------------------------------------

class Node:
    def __str__(self) -> str: ...
    def children(self) -> Tuple[Node, ...]: ...


# --- Arithmetic --------------------------------------------------------------

class ArithExpr(Node):
    @property
    def dtype(self) -> DType: ...
    def linearize(self) -> LinearArithExpr: ...

class Var(ArithExpr):
    @property
    def name(self) -> str: ...
    @property
    def indices(self) -> List[int]: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def kind(self) -> SymbolKind: ...
    @property
    def onnx_name(self) -> Optional[str]: ...
    @property
    def network_name(self) -> str: ...
    @property
    def line(self) -> int: ...
    def linearize(self) -> LinearArithExpr: ...

class Literal(ArithExpr):
    @property
    def lexeme(self) -> str: ...
    @property
    def line(self) -> int: ...

class Float(ArithExpr):
    @property
    def value(self) -> float: ...

class Int(ArithExpr):
    @property
    def value(self) -> int: ...

class IntExpr(ArithExpr):
    @property
    def value(self) -> int: ...
    @property
    def lexeme(self) -> str: ...

class Negate(ArithExpr):
    @property
    def expr(self) -> ArithExpr: ...

class Plus(ArithExpr):
    @property
    def args(self) -> Tuple[ArithExpr, ...]: ...

class Minus(ArithExpr):
    @property
    def head(self) -> ArithExpr: ...
    @property
    def rest(self) -> Tuple[ArithExpr, ...]: ...

class Multiply(ArithExpr):
    @property
    def args(self) -> Tuple[ArithExpr, ...]: ...


# --- Linear Arithmetic -------------------------------------------------------

class Term:
    @property
    def coeff(self) -> float: ...
    @property
    def var_name(self) -> str: ...
    @property
    def var(self) -> Var: ...

class LinearArithExpr:
    @property
    def terms(self) -> List[Term]: ...
    @property
    def constant(self) -> float: ...


# --- Boolean -----------------------------------------------------------------

class BoolExpr(Node):
    def dnf_form(self) -> List[List[BoolExpr]]: ...
    def children(self) -> List[BoolExpr]: ...

class Compare(BoolExpr):
    @property
    def lhs(self) -> ArithExpr: ...
    @property
    def rhs(self) -> ArithExpr: ...

class GreaterThan(Compare): ...
class LessThan(Compare): ...
class GreaterEqual(Compare): ...
class LessEqual(Compare): ...
class Equal(Compare): ...
class NotEqual(Compare): ...

class Connective(BoolExpr):
    @property
    def args(self) -> Tuple[BoolExpr, ...]: ...

class And(BoolExpr): ...
class Or(BoolExpr): ...


# --- Assertions --------------------------------------------------------------

class Assertion(Node):
    @property
    def expr(self) -> BoolExpr: ...


# --- Declarations ------------------------------------------------------------

class InputDefinition(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def kind(self) -> SymbolKind: ...
    @property
    def onnx_name(self) -> Optional[str]: ...
    @property
    def network_name(self) -> str: ...

class HiddenDefinition(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def kind(self) -> SymbolKind: ...
    @property
    def onnx_name(self) -> Optional[str]: ...
    @property
    def network_name(self) -> str: ...

class OutputDefinition(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def kind(self) -> SymbolKind: ...
    @property
    def onnx_name(self) -> Optional[str]: ...
    @property
    def network_name(self) -> str: ...


# --- Network ---------------------------------------------------------

class Network(Node):
    @property
    def name(self) -> str: ...
    @property
    def equal_to(self) -> str: ...
    @property
    def isometric_to(self) -> str: ...
    @property
    def inputs(self) -> Tuple[InputDefinition, ...]: ...
    @property
    def hidden(self) -> Tuple[HiddenDefinition, ...]: ...
    @property
    def outputs(self) -> Tuple[OutputDefinition, ...]: ...


# --- Version -----------------------------------------------------------

class Version(Node):
    @property
    def major(self) -> int: ...
    @property
    def minor(self) -> int: ...


class Query(Node):
    @property
    def networks(self) -> Tuple[Network, ...]: ...
    @property
    def assertions(self) -> Tuple[Assertion, ...]: ...


# --- Compatibility (Reachability Format) ------------------------------------

class Polytope:
    @property
    def coeff_matrix(self) -> List[List[float]]: ...
    @property
    def rhs(self) -> List[float]: ...

class SpecCase:
    @property
    def input_box(self) -> List[Tuple[float, float]]: ...
    @property  
    def output_constraints(self) -> List[Polytope]: ...


# --- Parse API (typed) -------------------------------------------------------

def parse_vnnlib(path: str) -> Query: ...
def parse_vnnlib_str(content: str) -> Query: ...
def transform_to_compat(query: Query) -> List[SpecCase]: ...

__version__: str
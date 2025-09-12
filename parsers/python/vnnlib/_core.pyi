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

class VarExpr(ArithExpr):
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
    def args(self) -> List[ArithExpr]: ...

class Minus(ArithExpr):
    @property
    def head(self) -> ArithExpr: ...
    @property
    def rest(self) -> List[ArithExpr]: ...

class Multiply(ArithExpr):
    @property
    def args(self) -> List[ArithExpr]: ...


# --- Boolean -----------------------------------------------------------------

class BoolExpr(Node): ...

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
    def args(self) -> List[BoolExpr]: ...

class And(Connective): ...
class Or(Connective): ...


# --- Assertions --------------------------------------------------------------

class Assertion(Node):
    @property
    def cond(self) -> BoolExpr: ...


# --- Declarations ------------------------------------------------------------

class Input(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def onnx_name(self) -> Optional[str]: ...

class Hidden(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def onnx_name(self) -> Optional[str]: ...

class Output(Node):
    @property
    def name(self) -> str: ...
    @property
    def dtype(self) -> DType: ...
    @property
    def shape(self) -> Shape: ...
    @property
    def onnx_name(self) -> Optional[str]: ...


# --- Network ---------------------------------------------------------

class Network(Node):
    @property
    def name(self) -> str: ...
    @property
    def equal_to(self) -> str: ...
    @property
    def isomorphic_to(self) -> str: ...
    @property
    def inputs(self) -> List[Input]: ...
    @property
    def hidden(self) -> List[Hidden]: ...
    @property
    def outputs(self) -> List[Output]: ...


# --- Version -----------------------------------------------------------

class Version(Node):
    @property
    def major(self) -> int: ...
    @property
    def minor(self) -> int: ...


class Query(Node):
    @property
    def networks(self) -> List[Network]: ...
    @property
    def assertions(self) -> List[Assertion]: ...


# --- Parse API (typed) -------------------------------------------------------

def parse_vnnlib_typed(path: str) -> Query: ...
def parse_vnnlib_str_typed(content: str) -> Query: ...

__version__: str
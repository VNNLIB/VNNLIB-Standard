module VNNLib where

open import Data.List
open import Data.String hiding (map)
open import Data.Nat
open import Data.Integer
open import Data.Rational as ℚ
open import Data.Bool

-- Tokens
-- -- UNUSED
data SDouble : Set where
  mkSDouble : String → SDouble

data SInt : Set where
  mkSInt : String → SInt

-- -- Naming/referencing
data TensorElement : Set where
  STensorElement : String → TensorElement

data VariableName : Set where
  SVariableName : String → VariableName

-- Tensor Shape (replaces Int in syntax)
data TensorShape : Set where
  shape : List ℕ → TensorShape

-- Arithmetic Expressions: nary operations
data ArithExpr : Set where
  const : ℚ → ArithExpr
  add : List ArithExpr → ArithExpr
  negate : List ArithExpr → ArithExpr
  mult : List ArithExpr → ArithExpr

⟦_⟧ : ArithExpr → ℚ
⟦ const e ⟧ = e
⟦ add [] ⟧ = 0ℚ
⟦ add (e ∷ xe) ⟧ = ℚ._+_ ⟦ e ⟧ ⟦ add xe ⟧
⟦ mult [] ⟧ = 1ℚ
⟦ mult (e ∷ xe) ⟧ = ℚ._*_ ⟦ e ⟧ ⟦ mult xe ⟧
⟦ negate [] ⟧ = 0ℚ
⟦ negate (e ∷ xe) ⟧ = ℚ._-_ ⟦ e ⟧ ⟦ negate xe ⟧

-- Boolean Expressions: Connective and Comparative Expressions
data BoolExpr : Set where
  literal : Bool → BoolExpr
  -- Comparative Expressions: 2-ary operations
  greaterThan    : ArithExpr → ArithExpr → BoolExpr
  lessThan       : ArithExpr → ArithExpr → BoolExpr
  greaterEqual   : ArithExpr → ArithExpr → BoolExpr
  lessEqual      : ArithExpr → ArithExpr → BoolExpr
  notEqual       : ArithExpr → ArithExpr → BoolExpr
  equal          : ArithExpr → ArithExpr → BoolExpr
  -- Connective Expressions
  andExpr : List BoolExpr → BoolExpr
  orExpr  : List BoolExpr → BoolExpr


<_> : BoolExpr → Bool
< literal e > = e 
< greaterThan e1 e2 > = not ( ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧ )
< lessThan e1 e2 > = ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧ ∧ not ( ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧ ∧ ℚ._≤ᵇ_ ⟦ e2 ⟧ ⟦ e1 ⟧ )
< greaterEqual e1 e2 > = ℚ._≤ᵇ_ ⟦ e2 ⟧ ⟦ e1 ⟧
< lessEqual e1 e2 > = ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧
< notEqual e1 e2 > = not ( ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧ ∧ ℚ._≤ᵇ_ ⟦ e2 ⟧ ⟦ e1 ⟧ )
< equal e1 e2 > = ℚ._≤ᵇ_ ⟦ e1 ⟧ ⟦ e2 ⟧ ∧ ℚ._≤ᵇ_ ⟦ e2 ⟧ ⟦ e1 ⟧
< andExpr [] > = true
< andExpr (e ∷ xe) > = _∧_ < e > < andExpr xe >
< orExpr [] > = false
< orExpr (e ∷ xe) > = _∨_ < e > < orExpr xe >

-- Properties: evalute to true or false
data Property : Set where
  assert : BoolExpr → Property

%_% : Property → Bool
% assert p % = < p >

-- Element Types
data ElementType : Set where
  real         : ElementType
  float16      : ElementType
  float32      : ElementType
  float64      : ElementType
  bfloat16     : ElementType
  float8e4m3fn : ElementType
  float8e5m2   : ElementType
  float8e4m3fnuz : ElementType
  float8e5m2fnuz : ElementType
  float4e2m1   : ElementType
  int8         : ElementType
  int16        : ElementType
  int32        : ElementType
  int64        : ElementType
  uint8        : ElementType
  uint16       : ElementType
  uint32       : ElementType
  uint64       : ElementType
  complex64    : ElementType
  complex128   : ElementType
  boolType     : ElementType
  stringType   : ElementType

-- Tensor Definitions
data InputDefinition : Set where
  declareInput : VariableName → ElementType → TensorShape → InputDefinition

data IntermediateDefinition : Set where
  declareIntermediate : VariableName → ElementType → TensorShape → String → IntermediateDefinition

data OutputDefinition : Set where
  declareOutput : VariableName → ElementType → TensorShape → OutputDefinition

-- Network Definitions
data NetworkDefinition : Set where
  declareNetwork : VariableName → List InputDefinition → List IntermediateDefinition → List OutputDefinition → NetworkDefinition

-- Queries
data Query : Set where
  mkQuery : List NetworkDefinition → List Property → Query

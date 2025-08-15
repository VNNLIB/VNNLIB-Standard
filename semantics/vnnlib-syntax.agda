
module vnnlib-syntax where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat as ℕ
open import Data.Rational as ℚ
open import Data.Fin as Fin
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Bool

open import tensor using (TensorShape; TensorIndices)

-- Variables
--  -- Naming/referencing
data VariableName : Set where
  SVariableName : String → VariableName

-- -- Element Types
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


-- Declarations are used to contruct the context
-- -- Each entry in the context is a network type
record NetworkType : Set where
  constructor
    networkType
  field
    inputShape : List TensorShape
    outputShape : List TensorShape


-- Node Definitions
data InputDefinition : Set where
  declareInput : VariableName → ElementType → TensorShape → InputDefinition

-- data IntermediateDefinition : Set where
  -- declareIntermediate : VariableName → ElementType → TensorShape → String → IntermediateDefinition

data OutputDefinition : Set where
  declareOutput : VariableName → ElementType → TensorShape → OutputDefinition

-- Network Definitions
data NetworkDefinition : Set where
  declareNetwork : VariableName → List InputDefinition → List OutputDefinition → NetworkDefinition

-- Context is a list of network types
Context : Set
Context = List (NetworkType)

-- Network definitions are used to create the context
mkContext : List NetworkDefinition → Context
mkContext [] = []
mkContext (declareNetwork _ inputs outputs ∷ tail) =
  networkType
    (List.map (λ { (declareInput _ _ shape) → shape }) inputs)
    (List.map (λ { (declareOutput _ _ shape) → shape }) outputs)
  ∷ mkContext tail


-- Assertions
module _ (Γ : Context) where
-- Arithmetic Expressions: nary operations
  data ArithExpr : Set where
    constant  : ℚ → ArithExpr
    negate : ArithExpr → ArithExpr 
    varInput : (i : Fin (List.length Γ)) → (j : Fin ( List.length (NetworkType.inputShape (List.lookup Γ i)) ) ) →
      TensorIndices (List.lookup (NetworkType.inputShape (List.lookup Γ i)) j ) → ArithExpr
    varOutput : (i : Fin (List.length Γ)) →  (j : Fin ( List.length (NetworkType.outputShape (List.lookup Γ i)) ) ) →
      TensorIndices (List.lookup (NetworkType.outputShape (List.lookup Γ i)) j)  → ArithExpr
    add : List (ArithExpr) → ArithExpr
    minus : List (ArithExpr) → ArithExpr
    mult  : List (ArithExpr) → ArithExpr

  -- Boolean Expressions: Connective and Comparative Expressions
  data BoolExpr : Set where
    literal : Bool → BoolExpr
    -- Comparative Expressions: 2-ary operations
    greaterThan    : ArithExpr → ArithExpr → BoolExpr
    -- Come up with consistent length names
    lessThan       : ArithExpr → ArithExpr → BoolExpr
    greaterEqual   : ArithExpr → ArithExpr → BoolExpr
    lessEqual      : ArithExpr → ArithExpr → BoolExpr
    notEqual       : ArithExpr → ArithExpr → BoolExpr
    equal          : ArithExpr → ArithExpr → BoolExpr
    -- Connective Expressions
    andExpr : List (BoolExpr) → BoolExpr
    orExpr  : List (BoolExpr) → BoolExpr

  -- Properties: evalute to true or false
  data Property : Set where
    assert : BoolExpr → Property


-- Query
data Query : Set where
  mkQuery : (networks : List NetworkDefinition) → List (Property (mkContext networks)) → Query

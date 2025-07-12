
module vnnlib-syntax where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat as ℕ

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

-- -- Tensor Shape
TensorShape : Set
TensorShape = List ℕ


-- Declarations are used to contruct the context
-- -- Each entry in the context is a network type
record NetworkType : Set where
  constructor
    networkType
  field
    inputShape : List TensorShape
    outputShape : List TensorShape

-- Context is a list of network types
Context : Set
Context = List (NetworkType)


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

-- Network definitions are used to create the context
mkContext : List NetworkDefinition → Context
mkContext [] = []
mkContext (declareNetwork _ inputs outputs ∷ tail) =
  networkType
    (List.map (λ { (declareInput _ _ shape) → shape }) inputs)
    (List.map (λ { (declareOutput _ _ shape) → shape }) outputs)
  ∷ mkContext tail


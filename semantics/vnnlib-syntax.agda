
module vnnlib-syntax where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat as ℕ
open import Data.Rational as ℚ
open import Data.Fin as Fin
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Bool

open import vnnlib-types using (ElementType; ElementTypeToSet)
open import tensor using (TensorShape; TensorIndices)

-- Variables
--  -- Naming/referencing
data VariableName : Set where
  SVariableName : String → VariableName

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

convertInputΓ : InputDefinition → TensorShape
convertInputΓ (declareInput _ _ x₂) = x₂

convertOutputΓ : OutputDefinition → TensorShape
convertOutputΓ (declareOutput _ _ x₂) = x₂

convertNetworkΓ : NetworkDefinition → NetworkType
convertNetworkΓ (declareNetwork _ inputs₁ outputs₁) = networkType (List.map convertInputΓ inputs₁) (List.map convertOutputΓ outputs₁)

-- Network definitions are used to create the context
mkContext : List NetworkDefinition → Context
mkContext networkDefinitions = List.map convertNetworkΓ networkDefinitions

-- Assertions
module _ (Γ : Context) where
-- Arithmetic Expressions: nary operations
  data ArithExpr (τ : ElementType) : Set where
    constant : ElementTypeToSet τ → ArithExpr τ
    negate : ArithExpr τ → ArithExpr τ 
    varInput : (i : Fin (List.length Γ)) → (j : Fin ( List.length (NetworkType.inputShape (List.lookup Γ i)) ) ) →
      TensorIndices (List.lookup (NetworkType.inputShape (List.lookup Γ i)) j ) → ArithExpr τ
    varOutput : (i : Fin (List.length Γ)) →  (j : Fin ( List.length (NetworkType.outputShape (List.lookup Γ i)) ) ) →
      TensorIndices (List.lookup (NetworkType.outputShape (List.lookup Γ i)) j)  → ArithExpr τ
    add : List (ArithExpr τ) → ArithExpr τ
    minus : List (ArithExpr τ) → ArithExpr τ
    mult  : List (ArithExpr τ) → ArithExpr τ

  -- Boolean Expressions: Connective and Comparative Expressions
  data BoolExpr (τ : ElementType) : Set where
    literal : Bool → BoolExpr τ
    -- Comparative Expressions: 2-ary operations
    greaterThan    : ArithExpr τ → ArithExpr τ → BoolExpr τ
    -- Come up with consistent length names
    lessThan       : ArithExpr τ → ArithExpr τ → BoolExpr τ
    greaterEqual   : ArithExpr τ → ArithExpr τ → BoolExpr τ
    lessEqual      : ArithExpr τ → ArithExpr τ → BoolExpr τ
    notEqual       : ArithExpr τ → ArithExpr τ → BoolExpr τ
    equal          : ArithExpr τ → ArithExpr τ → BoolExpr τ
    -- Connective Expressions
    andExpr : List (BoolExpr τ) → BoolExpr τ
    orExpr  : List (BoolExpr τ) → BoolExpr τ

  -- Assertions : evalute to true or false
  data Assertion : Set where
    assert : BoolExpr {!!} → Assertion


-- Query
data Query : Set where
  mkQuery : (networks : List NetworkDefinition) → List (Assertion (mkContext networks)) → Query

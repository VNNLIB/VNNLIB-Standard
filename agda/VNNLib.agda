module VNNLib where

open import Data.List
open import Data.String hiding (map)
open import Data.Nat
open import Data.Integer
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Fin

Context : Set
Context = ℕ

Environment : Context → Set
Environment Γ = Fin Γ → ℚ

-- -- Naming/referencing

data VariableName : Set where
  SVariableName : String → VariableName

-- Tensor Shape (replaces Int in syntax)
data TensorShape : Set where
  shape : List ℕ → TensorShape

-- Arithmetic Expressions: nary operations
data ArithExpr (Γ : Context) : Set where
  const  : ℚ → ArithExpr Γ
  negate : ArithExpr Γ → ArithExpr Γ 
  var : Fin Γ → ArithExpr Γ
  add : List (ArithExpr Γ) → ArithExpr Γ
  minus : List (ArithExpr Γ) → ArithExpr Γ
  mult  : List (ArithExpr Γ) → ArithExpr Γ

-- Arithmetic Expression Evaluation
⟦_%_%_⟧ₐ : (Γ : Context) → Environment (Γ) → ArithExpr (Γ) → ℚ
⟦ Γ % ε % (const a) ⟧ₐ  = a
⟦ Γ % ε % (negate a) ⟧ₐ = 0ℚ ℚ.- ⟦ Γ % ε % a ⟧ₐ 
⟦ Γ % ε % (var a) ⟧ₐ    = ε a
⟦ Γ % ε % (add []) ⟧ₐ   = 0ℚ
⟦ Γ % ε % (add (a ∷ ax)) ⟧ₐ   = ⟦ Γ % ε % a ⟧ₐ ℚ.+ ⟦ Γ % ε % (add ax) ⟧ₐ
⟦ Γ % ε % (mult []) ⟧ₐ  = 1ℚ
⟦ Γ % ε % (mult (a ∷ ax)) ⟧ₐ  = ⟦ Γ % ε % a ⟧ₐ ℚ.* ⟦ Γ % ε % (mult ax) ⟧ₐ
⟦ Γ % ε % (minus []) ⟧ₐ = 0ℚ
⟦ Γ % ε % (minus (a ∷ ax)) ⟧ₐ = ⟦ Γ % ε % a ⟧ₐ ℚ.- ⟦ Γ % ε % (minus ax) ⟧ₐ

-- Boolean Expressions: Connective and Comparative Expressions
data BoolExpr (Γ : Context) : Set where
  literal : Bool → BoolExpr Γ
  -- Comparative Expressions: 2-ary operations
  greaterThan    : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  lessThan       : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  greaterEqual   : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  lessEqual      : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  notEqual       : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  equal          : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  -- Connective Expressions
  andExpr : List (BoolExpr Γ) → BoolExpr Γ
  orExpr  : List (BoolExpr Γ) → BoolExpr Γ

⟦_%_%_⟧ᵇ : (Γ : Context) → Environment (Γ) → BoolExpr (Γ) → Bool
⟦ Γ % ε % (literal b) ⟧ᵇ = b
⟦ Γ % ε % (greaterThan a1 a2) ⟧ᵇ  = not ( ⟦ Γ % ε % a1 ⟧ₐ ℚ.≤ᵇ ⟦ Γ % ε % a2 ⟧ₐ )
⟦ Γ % ε % (lessThan a1 a2) ⟧ᵇ = not (ℚ._≤ᵇ_ ⟦ Γ % ε % a2 ⟧ₐ ⟦ Γ % ε % a1 ⟧ₐ )
⟦ Γ % ε % (greaterEqual a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ Γ % ε % a2 ⟧ₐ ⟦ Γ % ε % a1 ⟧ₐ
⟦ Γ % ε % (lessEqual a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ Γ % ε % a1 ⟧ₐ ⟦ Γ % ε % a2 ⟧ₐ
⟦ Γ % ε % (notEqual a1 a2) ⟧ᵇ  = not ( ℚ._≤ᵇ_ ⟦ Γ % ε % a1 ⟧ₐ ⟦ Γ % ε % a2 ⟧ₐ ∧ ℚ._≤ᵇ_ ⟦ Γ % ε % a2 ⟧ₐ ⟦ Γ % ε % a1 ⟧ₐ )
⟦ Γ % ε % (equal a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ Γ % ε % a1 ⟧ₐ ⟦ Γ % ε % a2 ⟧ₐ ∧ ℚ._≤ᵇ_ ⟦ Γ % ε % a2 ⟧ₐ ⟦ Γ % ε % a1 ⟧ₐ
⟦ Γ % ε % (andExpr []) ⟧ᵇ  = true
⟦ Γ % ε % (andExpr (b ∷ xb)) ⟧ᵇ = _∧_ ⟦ Γ % ε % b ⟧ᵇ ⟦ Γ % ε % (andExpr xb) ⟧ᵇ
⟦ Γ % ε % (orExpr []) ⟧ᵇ = false
⟦ Γ % ε % (orExpr (b ∷ xb)) ⟧ᵇ  = _∨_ ⟦ Γ % ε % b ⟧ᵇ ⟦ Γ % ε % (orExpr xb) ⟧ᵇ

-- Properties: evalute to true or false
data Property (Γ : Context) : Set where
  assert : BoolExpr Γ → Property Γ

⟦_%_%_⟧ₚ : (Γ : Context) → Environment (Γ) → Property (Γ) → Bool
⟦ Γ % ε % (assert p) ⟧ₚ = ⟦ Γ % ε % p ⟧ᵇ

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

-- TODO: Does not pass type-check
-- Queries
-- data Query : Set where
-- -- mkQuery : List NetworkDefinition → List Property → Query

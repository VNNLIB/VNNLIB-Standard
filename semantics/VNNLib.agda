module VNNLib where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat
open import Data.Integer
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Fin
open import Data.Product as Product

-- Tensor Shape (replaces Int in syntax)
data TensorShape : Set where
  shape : List ℕ → TensorShape

postulate Tensor : TensorShape → Set

postulate GetTensorElement : ∀ {shape} → (indices : List ℕ) → Tensor shape → ℚ 

Context : Set
Context = List (TensorShape × TensorShape)

Environment : Context → Set
Environment Γ =
  (i : Fin (List.length Γ)) →
  let (inputShape , outputShape) = List.lookup Γ i in
  (Tensor inputShape → Tensor outputShape) × Tensor inputShape

-- -- Naming/referencing

data VariableName : Set where
  SVariableName : String → VariableName


-- Arithmetic Expressions: nary operations
data ArithExpr (Γ : Context) : Set where
  const  : ℚ → ArithExpr Γ
  negate : ArithExpr Γ → ArithExpr Γ
  varInput : Fin (List.length Γ) → List ℕ → ArithExpr Γ
  varOutput : Fin (List.length Γ) → List ℕ → ArithExpr Γ
  add : List (ArithExpr Γ) → ArithExpr Γ
  minus : List (ArithExpr Γ) → ArithExpr Γ
  mult  : List (ArithExpr Γ) → ArithExpr Γ

-- Arithmetic Expression Evaluation         
⟦_%_⟧ₐ : ∀ {Γ} → Environment Γ → ArithExpr Γ → ℚ
⟦ ε % (const a) ⟧ₐ  = a
⟦ ε % (negate a) ⟧ₐ = 0ℚ ℚ.- ⟦ ε % a ⟧ₐ 
⟦ ε % (varInput n i ) ⟧ₐ  = GetTensorElement i (Product.proj₂ (ε n))
⟦ ε % (varOutput n i ) ⟧ₐ = GetTensorElement i ((Product.proj₁ (ε n)) (Product.proj₂ ((ε n))))
-- Cannot simplify similar cases with fold as context is implicit
⟦ ε % (add []) ⟧ₐ   = 0ℚ
⟦ ε % (add (a ∷ ax)) ⟧ₐ   = ⟦ ε % a ⟧ₐ ℚ.+ ⟦ ε % (add ax) ⟧ₐ
⟦ ε % (mult []) ⟧ₐ  = 1ℚ
⟦ ε % (mult (a ∷ ax)) ⟧ₐ  = ⟦ ε % a ⟧ₐ ℚ.* ⟦ ε % (mult ax) ⟧ₐ
⟦ ε % (minus []) ⟧ₐ = 0ℚ
⟦ ε % (minus (a ∷ ax)) ⟧ₐ = ⟦ ε % a ⟧ₐ ℚ.- ⟦ ε % (minus ax) ⟧ₐ




-- Boolean Expressions: Connective and Comparative Expressions
data BoolExpr (Γ : Context) : Set where
  literal : Bool → BoolExpr Γ
  -- Comparative Expressions: 2-ary operations
  greaterThan    : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  -- Come up with consistent length names
  lessThan       : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  greaterEqual   : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  lessEqual      : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  notEqual       : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  equal          : ArithExpr Γ → ArithExpr Γ → BoolExpr Γ
  -- Connective Expressions
  andExpr : List (BoolExpr Γ) → BoolExpr Γ
  orExpr  : List (BoolExpr Γ) → BoolExpr Γ


⟦_%_⟧ᵇ : ∀ {Γ} → Environment Γ → BoolExpr Γ → Bool
⟦ ε % (literal b) ⟧ᵇ = b
⟦ ε % (greaterThan a1 a2) ⟧ᵇ  = not ( ⟦ ε % a1 ⟧ₐ ℚ.≤ᵇ ⟦ ε % a2 ⟧ₐ )
⟦ ε % (lessThan a1 a2) ⟧ᵇ = not (ℚ._≤ᵇ_ ⟦ ε % a2 ⟧ₐ ⟦ ε % a1 ⟧ₐ )
⟦ ε % (greaterEqual a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ ε % a2 ⟧ₐ ⟦ ε % a1 ⟧ₐ
⟦ ε % (lessEqual a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ ε % a1 ⟧ₐ ⟦ ε % a2 ⟧ₐ
⟦ ε % (notEqual a1 a2) ⟧ᵇ  = not ( ℚ._≤ᵇ_ ⟦ ε % a1 ⟧ₐ ⟦ ε % a2 ⟧ₐ ∧ ℚ._≤ᵇ_ ⟦ ε % a2 ⟧ₐ ⟦ ε % a1 ⟧ₐ )
⟦ ε % (equal a1 a2) ⟧ᵇ = ℚ._≤ᵇ_ ⟦ ε % a1 ⟧ₐ ⟦ ε % a2 ⟧ₐ ∧ ℚ._≤ᵇ_ ⟦ ε % a2 ⟧ₐ ⟦ ε % a1 ⟧ₐ
⟦ ε % (andExpr []) ⟧ᵇ  = true
⟦ ε % (andExpr (b ∷ xb)) ⟧ᵇ = _∧_ ⟦ ε % b ⟧ᵇ ⟦ ε % (andExpr xb) ⟧ᵇ
⟦ ε % (orExpr []) ⟧ᵇ = false
⟦ ε % (orExpr (b ∷ xb)) ⟧ᵇ  = _∨_ ⟦ ε % b ⟧ᵇ ⟦ ε % (orExpr xb) ⟧ᵇ

-- Properties: evalute to true or false
data Property (Γ : Context) : Set where
  assert : BoolExpr Γ → Property Γ

⟦_%_⟧ₚ : ∀ {Γ} → Environment Γ → Property Γ → Bool
⟦ ε % (assert p) ⟧ₚ = ⟦ ε % p ⟧ᵇ

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

-- data IntermediateDefinition : Set where
  -- declareIntermediate : VariableName → ElementType → TensorShape → String → IntermediateDefinition

data OutputDefinition : Set where
  declareOutput : VariableName → ElementType → TensorShape → OutputDefinition

-- Network Definitions
data NetworkDefinition : Set where
  declareNetwork : VariableName → List InputDefinition → List OutputDefinition → NetworkDefinition

-- Use network definitions to create the context
mkContext : List NetworkDefinition → Context
mkContext [] = []
mkContext (declareNetwork _ (declareInput _ _ inputShape ∷ _) (declareOutput _ _ outputShape ∷ _) ∷ networksₙ₋₁) = (inputShape , outputShape) ∷ mkContext networksₙ₋₁
mkContext (_ ∷ networksₙ₋₁ ) = mkContext networksₙ₋₁

-- Query
data Query : Set where
  mkQuery : (networks : List NetworkDefinition) → List (Property (mkContext networks)) → Query

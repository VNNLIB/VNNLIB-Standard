module vnnlib-semantics where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat as ℕ hiding (_<ᵇ_)
open import Data.Integer
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Product.Nary.NonDependent as Nary
open import Data.Fin as Fin
open import Data.Product as Product
open import utils using (_≥ᵇ_;_>ᵇ_;_<ᵇ_;_=ᵇ_;_≠ᵇ_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Level
open import Function.Nary.NonDependent as NFunc
open import Function.Base

open import vnnlib-syntax using (TensorShape; NetworkType; NetworkDefinition; Context; mkContext)

-- Tensor
data TensorIndices : TensorShape → Set where
 empty : TensorIndices []
 non-empty : {head : ℕ} → {tail : List ℕ} → Fin head →  TensorIndices tail → TensorIndices (head ∷ tail) 

data Tensor (Σ : Set) : TensorShape → Set where
  scalar : Σ → Tensor Σ []
  vector : {head : ℕ} → {tail : List ℕ} → Vec (Tensor Σ tail) head → Tensor Σ (head ∷ tail)

TensorElement : ∀ {shape} → TensorIndices shape → Tensor ℚ shape → ℚ
TensorElement {[]} empty (scalar x) = x
TensorElement {dim ∷ shape} (non-empty idx idxs) (vector x) = TensorElement idxs (Vec.lookup x idx)

testSide₁ : Tensor ℚ (2 ∷ 2 ∷ [])
testSide₁ = vector (vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷
                 vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷ [])

testSide₂ : Tensor ℚ (2 ∷ 2 ∷ [])
testSide₂ = vector (vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷
                 vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷ [])

testTensor : Tensor ℚ (2 ∷ 2 ∷ 2 ∷ [])
testTensor = vector (testSide₁ ∷ testSide₂ ∷ [])

testIndex : TensorIndices (2 ∷ 2 ∷ 2 ∷ [])
testIndex = non-empty (# 1) (non-empty (# 1) (non-empty ((# 1)) empty))

testElement : ℚ
testElement = TensorElement testIndex testTensor


-- Pending on std-lib update from vehicle-lang/vehicle-formalisation
stabulate : ∀ n → (f : Fin n → Level) → (g : (i : Fin n) → Set (f i)) → Sets n (ltabulate n f)
stabulate ℕ.zero f g = _
stabulate (suc n) f g = g Fin.zero , stabulate n (f ∘′ Fin.suc) (λ u → g (Fin.suc u))

    
-- Network Implementation Representation
ProductOfTensorsLevel : List TensorShape → Level
ProductOfTensorsLevel shapes = NFunc.⨆ (List.length shapes ) (ltabulate (List.length shapes) (λ i → Level.zero))

ProductOfTensors : (shapes : List TensorShape) → Set (ProductOfTensorsLevel shapes) 
ProductOfTensors shapes = Nary.Product ni (stabulate ni (λ i → Level.zero) (λ i → Tensor ℚ (List.lookup shapes i)) )
  where ni = List.length shapes

record NetworkImplementation (networkType : NetworkType) : Set
       (ProductOfTensorsLevel (NetworkType.inputShape networkType) Level.⊔ ProductOfTensorsLevel (NetworkType.outputShape networkType)) where
  constructor
    network
  open NetworkType networkType
  field
    networkFunction : ProductOfTensors inputShape → ProductOfTensors outputShape
    inputTensors : ProductOfTensors inputShape


Environment : Context → Setω
Environment Γ =
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in NetworkImplementation networkType


-- Arithmetic Expressions: nary operations
data ArithExpr (Γ : Context) : Set where
  constant  : ℚ → ArithExpr Γ
  negate : ArithExpr Γ → ArithExpr Γ
  varInput : (i : Fin (List.length Γ)) → (j : Fin ( List.length (NetworkType.inputShape (List.lookup Γ i)) ) ) →
    TensorIndices (List.lookup (NetworkType.inputShape (List.lookup Γ i)) j ) → ArithExpr Γ
  varOutput : (i : Fin (List.length Γ)) →  (j : Fin ( List.length (NetworkType.outputShape (List.lookup Γ i)) ) ) →
    TensorIndices (List.lookup (NetworkType.outputShape (List.lookup Γ i)) j)  → ArithExpr Γ
  add : List (ArithExpr Γ) → ArithExpr Γ
  minus : List (ArithExpr Γ) → ArithExpr Γ
  mult  : List (ArithExpr Γ) → ArithExpr Γ

-- Arithmetic Expression Evaluation         
⟦_%_⟧ₐ : ∀ {Γ} → Environment Γ → ArithExpr Γ → ℚ
⟦ ε % (constant a) ⟧ₐ  = a
⟦ ε % (negate a) ⟧ₐ = 0ℚ ℚ.- ⟦ ε % a ⟧ₐ 
⟦ ε % (varInput i j n ) ⟧ₐ  = TensorElement n (projₙ {!!} {!!} {!!}) -- NetworkImplementation.inputTensors (ε i) 
⟦ ε % (varOutput i j n ) ⟧ₐ = TensorElement n (projₙ {!!} {!!} {!!}) -- NetworkImplementation.networkFunction (ε i) (NetworkImplementation.inputTensors (ε i))
-- Cannot simplify similar cases with fold as context is implicit
⟦ ε % (add []) ⟧ₐ   = 0ℚ
⟦ ε % (add (a₀ ∷ a)) ⟧ₐ   = ⟦ ε % a₀ ⟧ₐ ℚ.+ ⟦ ε % (add a) ⟧ₐ
⟦ ε % (mult []) ⟧ₐ  = 1ℚ
⟦ ε % (mult (a₀ ∷ a)) ⟧ₐ  = ⟦ ε % a₀ ⟧ₐ ℚ.* ⟦ ε % (mult a) ⟧ₐ
⟦ ε % (minus []) ⟧ₐ = 0ℚ
⟦ ε % (minus (a₀ ∷ a)) ⟧ₐ = ⟦ ε % a₀ ⟧ₐ ℚ.- ⟦ ε % (minus a) ⟧ₐ


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
⟦ ε % (greaterThan a1 a2) ⟧ᵇ  = ⟦ ε % a1 ⟧ₐ >ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (lessThan a1 a2) ⟧ᵇ = ⟦ ε % a1 ⟧ₐ <ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (greaterEqual a1 a2) ⟧ᵇ = ⟦ ε % a1 ⟧ₐ ≥ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (lessEqual a1 a2) ⟧ᵇ = ⟦ ε % a1 ⟧ₐ ℚ.≤ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (notEqual a1 a2) ⟧ᵇ  = ⟦ ε % a1 ⟧ₐ ≠ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (equal a1 a2) ⟧ᵇ = ⟦ ε % a1 ⟧ₐ =ᵇ ⟦ ε % a2 ⟧ₐ
⟦ ε % (andExpr []) ⟧ᵇ  = true
⟦ ε % (andExpr (b ∷ xb)) ⟧ᵇ = _∧_ ⟦ ε % b ⟧ᵇ ⟦ ε % (andExpr xb) ⟧ᵇ
⟦ ε % (orExpr []) ⟧ᵇ = false
⟦ ε % (orExpr (b ∷ xb)) ⟧ᵇ  = _∨_ ⟦ ε % b ⟧ᵇ ⟦ ε % (orExpr xb) ⟧ᵇ

-- Properties: evalute to true or false
data Property (Γ : Context) : Set where
  assert : BoolExpr Γ → Property Γ

⟦_%_⟧ₚ : ∀ {Γ} → Environment Γ → Property Γ → Bool
⟦ ε % (assert p) ⟧ₚ = ⟦ ε % p ⟧ᵇ


-- Query
data Query : Set where
  mkQuery : (networks : List NetworkDefinition) → List (Property (mkContext networks)) → Query


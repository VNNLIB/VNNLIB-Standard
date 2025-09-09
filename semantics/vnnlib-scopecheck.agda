module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product using (Σ; proj₁; proj₂; _,_)
open import Data.Bool as Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.String as String using (String; _==_)
open import Data.String.Properties
open import Data.Fin as Fin
open import Data.List as List hiding (lookup; foldl)
open import Data.List.NonEmpty as List⁺
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.Properties using (length-map)
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; module ≡-Reasoning)
open Eq.≡-Reasoning
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_)
open import Function
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import vnnlib-types as 𝐄
open import syntax-utils
open import types-utils
open import check
open import tensor as 𝐓
open import context-isomorphism


open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

module _ (Σ : CheckContext) where
  Γ : Context
  Γ = convertΣtoΓ Σ

  isTypedVariable : 𝐄.ElementType → VariableBinding → Bool
  isTypedVariable τ v with τ 𝐄.≟ getElementType v
  ... | yes p = true
  ... | no _ = false

  postulate validIndices : List 𝐁.Number → (s : 𝐓.TensorShape) → Result (𝐓.TensorIndices s)

  inferArithExprType : 𝐁.ArithExpr → Maybe 𝐄.ElementType
  inferArithExprType (varExpr x xs) with variableNetworkIndex x Σ
  ... | error _ = nothing
  ... | success n with variableIndexInNetworkᵢₙₚᵤₜ (proj₁ (List.lookup Σ n)) x
  ... | success i = just (getElementType (List.lookup (toList (NetworkBinding.inputs (proj₁ (List.lookup Σ n)))) i))
  ... | error _ with variableIndexInNetworkₒᵤₜₚᵤₜ (proj₁ (List.lookup Σ n)) x
  ... | success j = just (getElementType (List.lookup (toList (NetworkBinding.outputs (proj₁ (List.lookup Σ n)))) j))
  ... | error _ = nothing -- out-of-scope
  inferArithExprType (valExpr x) = nothing
  inferArithExprType (negate a) = inferArithExprType a
  inferArithExprType (plus as) = {!!}
  -- inferArithExprType (plus []) = nothing
  -- inferArithExprType (plus (x ∷ as)) with inferArithExprType x
  -- ... | nothing = inferArithExprType (plus as)
  -- ... | just t = just t
  inferArithExprType (minus a as) = List.foldl {!!} (inferArithExprType a) as
  inferArithExprType (multiply as) = List.foldl {!!} nothing as
  
  checkArithExpr : {τ : 𝐄.ElementType} → 𝐁.ArithExpr → Result (𝐕.ArithExpr Γ τ)
  checkArithExpr {τ} (valExpr x) with parseNumber τ x
  ... | just t = success (constant t)
  ... | nothing = error "Cannot parse number"
  checkArithExpr (varExpr x xs) with variableNetworkIndex x Σ
  ... | error _ = error ""
  ... | success n with variableIndexInNetworkᵢₙₚᵤₜ (proj₁ (List.lookup Σ n)) x
  ...   | success i = success (varInput networkInd inputInd {!!})
    where
      networkInd : Fin (List.length (Γ))
      networkInd = subst Fin (length-CheckContext-Context Σ) n      

      inputInd : Fin (List.length (NetworkType.inputShape (List.lookup Γ (subst Fin (length-CheckContext-Context Σ) n))))
      inputInd = subst Fin (length-inputs Σ n) i
      
  ... | error _ with variableIndexInNetworkₒᵤₜₚᵤₜ (proj₁ (List.lookup Σ n)) x
  ... | error _ = error ""
  ... | success o = success (varOutput networkInd outputInd {!!})
    where
      networkInd : Fin (List.length (Γ))
      networkInd = subst Fin (length-CheckContext-Context Σ) n
      
      outputInd : Fin (List.length (NetworkType.outputShape (List.lookup Γ (subst Fin (length-CheckContext-Context Σ) n))))
      outputInd = subst Fin (length-outputs Σ n) o
      
  checkArithExpr (negate a) with checkArithExpr a
  ... | error _ = error ""
  ... | success x = success (negate x)
  checkArithExpr (plus as) = List.foldl (λ z z₁ → {!!}) (error "") as
  checkArithExpr (minus a as) = List.foldl (λ z z₁ → {!!}) (checkArithExpr a) as
  checkArithExpr (multiply as) = List.foldl (λ z z₁ → {!!}) (error "") as

  -- check boolean expressions
  checkCompExpr : ({τ : 𝐄.ElementType} → 𝐕.ArithExpr Γ τ → 𝐕.ArithExpr Γ τ → 𝐕.BoolExpr Γ) → 𝐁.ArithExpr → 𝐁.ArithExpr → Result(𝐕.BoolExpr Γ)
  checkCompExpr f b₁ b₂ = do
    let type = findType b₁ b₂
    t₁ ← checkArithExpr {type} b₁
    t₂ ← checkArithExpr {type} b₂
    return (f t₁ t₂)
    where
    findType : 𝐁.ArithExpr → 𝐁.ArithExpr → 𝐄.ElementType
    findType b₁ b₂ with inferArithExprType b₁ |  inferArithExprType b₂
    ... | just x | just x₁ = x
    ... | just x | nothing = x
    ... | nothing | just x = x
    ... | nothing | nothing = real

  -- wrapper function for checkCompExpr
  checkComparative : ({τ : 𝐄.ElementType} → 𝐕.ArithExpr Γ τ → 𝐕.ArithExpr Γ τ → 𝐕.CompExpr Γ τ) → 𝐁.ArithExpr → 𝐁.ArithExpr → Result(𝐕.BoolExpr Γ)
  checkComparative f b₁ b₂ = checkCompExpr (λ x x₁ → compExpr (_ , f x x₁)) b₁ b₂
  
  checkBoolExpr : 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
  checkBoolExpr (greaterThan a₁ a₂) = checkComparative greaterThan a₁ a₂
  checkBoolExpr (lessThan a₁ a₂) = checkComparative lessThan a₁ a₂
  checkBoolExpr (greaterEqual a₁ a₂) = checkComparative greaterEqual a₁ a₂
  checkBoolExpr (lessEqual a₁ a₂) = checkComparative lessEqual a₁ a₂
  checkBoolExpr (notEqual a₁ a₂) = checkComparative notEqual a₁ a₂
  checkBoolExpr (equal a₁ a₂) = checkComparative equal a₁ a₂
  checkBoolExpr (BoolExpr.and bs) = {!!}
  checkBoolExpr (BoolExpr.or bs) = {!!} 

scopeCheckAssertions : (Σ : CheckContext) → List⁺ 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
scopeCheckAssertions Σ asserts = List⁺.foldl checkAssertₙ checkAssert asserts
  where
    checkAssert : 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
    checkAssert (assert b) with checkBoolExpr Σ b
    ... | error _ = error ""
    ... | success x = success (List.[ assert x ])
    checkAssertₙ : Result (List (𝐕.Assertion (convertΣtoΓ Σ))) → 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
    checkAssertₙ (error _) _ = error ""
    checkAssertₙ (success props) a with checkAssert a
    ... | error _ = error ""
    ... | success x = success (x ++ props)

-- Check Assertions from the constructed Scope Context
checkAssertions : List 𝐁.NetworkDefinition → List⁺ 𝐁.Assertion → Result 𝐕.Query
checkAssertions defs asserts with mkCheckContext defs
... | error _ = error ""
... | success Σ with scopeCheckAssertions Σ asserts
... | error _ = error ""
... | success x = success (𝐕.mkQuery checkedNetworkDefs x) -- mkCheckContext should return the networkdefs
  where
    checkedNetworkDefs : List 𝐕.NetworkDefinition
    checkedNetworkDefs = List.map proj₂ Σ

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ver ns as) = asserts⁺ (convertListToList⁺ as)
  where
    asserts⁺ : Result (List⁺ 𝐁.Assertion) → Result 𝐕.Query
    asserts⁺ (error _) = error "Cannot have no assertions"
    asserts⁺ (success x₁) = checkAssertions ns x₁

module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product using (Σ; proj₁; proj₂)
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
open import Function
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
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
  
  checkExpressionₐᵣᵢₜₕ : 𝐁.ArithExpr → Result (𝐕.ArithExpr Γ)
  checkExpressionₐᵣᵢₜₕ (varExpr x xs) with variableNetworkIndex x Σ
  ... | error _ = error ""
  ... | success n with variableIndexInNetworkᵢₙₚᵤₜ (proj₁ (List.lookup (toList Σ) n)) x
  ...   | success i = success (varInput networkInd inputInd {!!})
    where
      networkInd : Fin (List.length (Γ))
      networkInd = subst Fin (length-CheckContext-Context Σ) n      

      inputInd : Fin (List.length (NetworkType.inputShape (List.lookup Γ (subst Fin (length-CheckContext-Context Σ) n))))
      inputInd = subst Fin (length-inputs Σ n) i
      
  ... | error _ with variableIndexInNetworkₒᵤₜₚᵤₜ (proj₁ (List.lookup (toList Σ) n)) x
  ... | error _ = error ""
  ... | success o = success (varOutput networkInd outputInd {!!})
    where
      networkInd : Fin (List.length (Γ))
      networkInd = subst Fin (length-CheckContext-Context Σ) n
      
      outputInd : Fin (List.length (NetworkType.outputShape (List.lookup Γ (subst Fin (length-CheckContext-Context Σ) n))))
      outputInd = subst Fin (length-outputs Σ n) o
      
  checkExpressionₐᵣᵢₜₕ (negate a) with checkExpressionₐᵣᵢₜₕ a
  ... | error _ = error ""
  ... | success x = success (negate x)
  checkExpressionₐᵣᵢₜₕ (plus as) = List.foldl (λ z z₁ → {!!}) (error "") as
  checkExpressionₐᵣᵢₜₕ (minus a as) = List.foldl (λ z z₁ → {!!}) (checkExpressionₐᵣᵢₜₕ a) as
  checkExpressionₐᵣᵢₜₕ (multiply as) = List.foldl (λ z z₁ → {!!}) (error "") as
  -- BNFC literals as strings
  checkExpressionₐᵣᵢₜₕ (doubleExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ (sIntExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ (intExpr x) = {!!}

  -- check boolean expressions
  checkComparativeExpression : (𝐕.ArithExpr Γ → 𝐕.ArithExpr Γ → 𝐕.BoolExpr Γ) → 𝐁.ArithExpr → 𝐁.ArithExpr → Result(𝐕.BoolExpr Γ)
  checkComparativeExpression f b₁ b₂ with checkExpressionₐᵣᵢₜₕ b₁
  ... | error _ = error ""
  ... | success b₁ with checkExpressionₐᵣᵢₜₕ b₂
  ... | error _ = error ""
  ... | success b₂ = success (f b₁ b₂)
  
  checkExpressionᵇᵒᵒˡ : 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
  checkExpressionᵇᵒᵒˡ (BoolExpr.and bs) = {!!}
  checkExpressionᵇᵒᵒˡ (BoolExpr.or bs) = {!!}
  -- checkExpressionᵇᵒᵒˡ (BoolExpr.and []) = success (literal true)
  -- checkExpressionᵇᵒᵒˡ (BoolExpr.and (x ∷ bs)) with checkExpressionᵇᵒᵒˡ x
  -- ... | error = error
  -- ... | success x' with checkExpressionᵇᵒᵒˡ (BoolExpr.and bs)
  -- ... | error = error
  -- ... | success bs' = success (andExpr (x' ∷ bs' ∷ []))
  -- checkExpressionᵇᵒᵒˡ (BoolExpr.or bs) = {!!} -- List.foldl (connectives orExpr) (success (literal false)) bs
  --   where
  --     connectives : (List (𝐕.BoolExpr Γ) → 𝐕.BoolExpr Γ) → Result (𝐕.BoolExpr Γ) → 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
  --     connectives v error _ = error
  --     connectives v (success x) c with checkExpressionᵇᵒᵒˡ c
  --     ... | error = error
  --     ... | success c = success (v (c ∷ List.[ x ]))    
  checkExpressionᵇᵒᵒˡ (greaterThan a₁ a₂) = checkComparativeExpression greaterThan a₁ a₂
  checkExpressionᵇᵒᵒˡ (lessThan a₁ a₂) = checkComparativeExpression lessThan a₁ a₂
  checkExpressionᵇᵒᵒˡ (greaterEqual a₁ a₂) = checkComparativeExpression greaterEqual a₁ a₂
  checkExpressionᵇᵒᵒˡ (lessEqual a₁ a₂) = checkComparativeExpression lessEqual a₁ a₂
  checkExpressionᵇᵒᵒˡ (notEqual a₁ a₂) = checkComparativeExpression notEqual a₁ a₂
  checkExpressionᵇᵒᵒˡ (equal a₁ a₂) = checkComparativeExpression equal a₁ a₂

scopeCheckAssertions : (Σ : CheckContext) → List⁺ 𝐁.Assertion → Result (List (𝐕.Property (convertΣtoΓ Σ)))
scopeCheckAssertions Σ asserts = List⁺.foldl checkAssertₙ checkAssert asserts
  where
    checkAssert : 𝐁.Assertion → Result (List (𝐕.Property (convertΣtoΓ Σ)))
    checkAssert (assert b) with checkExpressionᵇᵒᵒˡ Σ b
    ... | error _ = error ""
    ... | success x = success (List.[ assert x ])
    checkAssertₙ : Result (List (𝐕.Property (convertΣtoΓ Σ))) → 𝐁.Assertion → Result (List (𝐕.Property (convertΣtoΓ Σ)))
    checkAssertₙ (error _) _ = error ""
    checkAssertₙ (success props) a with checkAssert a
    ... | error _ = error ""
    ... | success x = success (x ++ props)

-- Check Assertions from the constructed Scope Context
checkAssertions : List⁺ 𝐁.NetworkDefinition → List⁺ 𝐁.Assertion → Result 𝐕.Query
checkAssertions defs asserts with mkCheckContext defs
... | error _ = error ""
... | success Σ with scopeCheckAssertions Σ asserts
... | error _ = error ""
... | success x = success (𝐕.mkQuery checkedNetworkDefs x) -- mkCheckContext should return the networkdefs
  where
    checkedNetworkDefs : List 𝐕.NetworkDefinition
    checkedNetworkDefs = List.map proj₂ (toList Σ)

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ns as) = queries⁺ (convertListToList⁺ ns) (convertListToList⁺ as)
  where
    queries⁺ : Result (List⁺ 𝐁.NetworkDefinition) → Result (List⁺ 𝐁.Assertion) → Result 𝐕.Query
    queries⁺ (error _) asserts = error ""
    queries⁺ (success x) (error _) = error ""
    queries⁺ (success x) (success x₁) = checkAssertions x x₁

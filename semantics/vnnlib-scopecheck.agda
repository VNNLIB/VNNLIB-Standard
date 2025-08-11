
module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product
open import Data.Bool as Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.String as String using (String; _==_)
open import Data.String.Properties
open import Data.Fin as Fin
open import Data.List as List hiding (lookup; foldl)
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import syntax-utils
open import types-utils
open import check


module _ (Γ : Context) where
  -- check arithmetic expressions
  checkExpressionₐᵣᵢₜₕ : CheckContext → 𝐁.ArithExpr → 𝐕.ArithExpr Γ
  checkExpressionₐᵣᵢₜₕ Γ (varExpr x xs) = varInput {!!} {!!} {!!}
  checkExpressionₐᵣᵢₜₕ Γ (doubleExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (sIntExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (intExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (negate a) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (plus as) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (minus a as) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (multiply as) = {!!}

  -- check boolean expressions
  postulate checkExpressionᵇᵒᵒˡ : CheckContext → 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
  -- checkExpressionᵇᵒᵒˡ Γ (BoolExpr.and []) = literal true
  -- checkExpressionᵇᵒᵒˡ Γ (BoolExpr.and (x ∷ bs)) = andExpr (checkExpressionᵇᵒᵒˡ Γ x ∷ checkExpressionᵇᵒᵒˡ Γ (BoolExpr.and bs) ∷ [])
  -- checkExpressionᵇᵒᵒˡ Γ (BoolExpr.or []) = literal false
  -- checkExpressionᵇᵒᵒˡ Γ (BoolExpr.or (x ∷ bs)) = orExpr (checkExpressionᵇᵒᵒˡ Γ x ∷ checkExpressionᵇᵒᵒˡ Γ (BoolExpr.or bs) ∷ [])
  -- checkExpressionᵇᵒᵒˡ Γ (greaterThan a₁ a₂) = greaterThan (checkExpressionₐᵣᵢₜₕ Γ a₁) (checkExpressionₐᵣᵢₜₕ Γ a₂)
  -- checkExpressionᵇᵒᵒˡ Γ (lessThan a₁ a₂) = lessThan {!!} {!!}
  -- checkExpressionᵇᵒᵒˡ Γ (greaterEqual a₁ a₂) = {!!}
  -- checkExpressionᵇᵒᵒˡ Γ (lessEqual a₁ a₂) = {!!}
  -- checkExpressionᵇᵒᵒˡ Γ (notEqual a₁ a₂) = {!!}
  -- checkExpressionᵇᵒᵒˡ Γ (equal a₁ a₂) = {!!}

  scopeCheckAssertions : CheckContext → List⁺ 𝐁.Assertion → Result (List (𝐕.Property Γ))
  scopeCheckAssertions Γ (assert b ∷ tail₁) with checkExpressionᵇᵒᵒˡ Γ b
  ... | error = error
  ... | (success x) = {!!} 


-- Check Assertions from the constructed Scope Context
checkAssertions : List⁺ 𝐁.NetworkDefinition → List⁺ 𝐁.Assertion → Result 𝐕.Query
checkAssertions defs asserts with mkCheckContext defs
... | error = error
... | success x with scopeCheckAssertions (mkContext (convertNetworkDefs defs)) x asserts
... | error = error
... | success x = success (𝐕.mkQuery (convertNetworkDefs defs) x)

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ns as) = queries⁺ (convertListToList⁺ ns) (convertListToList⁺ as)
  where
    queries⁺ : Result (List⁺ 𝐁.NetworkDefinition) → Result (List⁺ 𝐁.Assertion) → Result 𝐕.Query
    queries⁺ error asserts = error
    queries⁺ (success x) error = error
    queries⁺ (success x) (success x₁) = checkAssertions x x₁

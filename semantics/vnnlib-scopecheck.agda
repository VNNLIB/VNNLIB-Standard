module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product
open import Data.Bool as Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.String as String using (String; _==_)
open import Data.String.Properties
open import Data.Fin as Fin
open import Data.List as List hiding (lookup; foldl)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import syntax-utils
open import types-utils

-- Context for scope checking
ScopeContext : Set
ScopeContext = List⁺ (𝐁.VariableName) -- × with 𝐁.TensorShape and Type

-- Returns True/False if variable name is in the defined context
doesVariableNameExist : ScopeContext → 𝐁.VariableName → Bool
doesVariableNameExist(head₁ ∷ []) name = ⟦ head₁ ⟧asString == ⟦ name ⟧asString
doesVariableNameExist (head₁ ∷ x ∷ tail₁) name = false ∨ (⟦ x ⟧asString == ⟦ name ⟧asString) ∨ (doesVariableNameExist (head₁ ∷ tail₁) name)

-- Create Context from network definitions
addToContextₙ : Result ScopeContext → 𝐁.VariableName → Result ScopeContext
addToContextₙ error varName = error
addToContextₙ (success x) varName = if doesVariableNameExist x varName then error else success (varName ∷⁺ x)

-- Utilized for the first network definition, to first construct the context
addVars₁ : List⁺ 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List⁺ 𝐁.OutputDefinition → Result ScopeContext
addVars₁ is hs os = Γ₃ 
  where
    Γ₁ = foldl (λ ctx i → addToContextₙ ctx (inputVars i)) (λ i → success (inputVars i ∷ [])) is       -- input definitions to Γ
    Γ₂ = List.foldl (λ ctx h → addToContextₙ ctx (hiddenVars h)) Γ₁ hs                                  -- then, hidden definitions to Γ
    Γ₃ = foldl (λ ctx o → addToContextₙ ctx (outputVars o)) (λ o → addToContextₙ Γ₂ (outputVars o)) os  -- finally, output definitions to Γ


addVarsₙ : Result ScopeContext → List⁺ 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List⁺ 𝐁.OutputDefinition → Result ScopeContext
addVarsₙ Γ is hs os = Γ₃
  where
    Γ₁ = foldl (λ ctx i → addToContextₙ ctx (inputVars i)) (λ i → addToContextₙ Γ (inputVars i)) is    -- input definitions to Γ
    Γ₂ = List.foldl (λ ctx h → addToContextₙ ctx (hiddenVars h)) Γ₁ hs                                 -- then, hidden definitions to Γ
    Γ₃ = foldl (λ ctx o → addToContextₙ ctx (outputVars o)) (λ o → addToContextₙ Γ (outputVars o)) os  -- finally, output definitions to Γ

-- Convert the input and output definitions from List to List⁺ i.e. inputs and outputs MUST be NonEmpty Lists
addDefinitionVarsToContext :
  (Result ScopeContext → List⁺ 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List⁺ 𝐁.OutputDefinition → Result ScopeContext) →
    Result ScopeContext → Result (List⁺ 𝐁.InputDefinition) → List 𝐁.HiddenDefinition → Result (List⁺ 𝐁.OutputDefinition) → Result ScopeContext
addDefinitionVarsToContext func Γ error h o = error
addDefinitionVarsToContext func Γ (success x) h error = error
addDefinitionVarsToContext func Γ (success x) h (success x₁) = func Γ x h x₁

-- Make the Scope Context with Network Definitions
mkScopeContext : List⁺ 𝐁.NetworkDefinition → Result ScopeContext
mkScopeContext networkDefs = List⁺.foldl addNetworkDefToContext (addNetworkDefToContext error) networkDefs
  where      
    addNetworkDefToContext : Result ScopeContext → 𝐁.NetworkDefinition → Result ScopeContext
    addNetworkDefToContext error (networkDef x is hs os) = error
    addNetworkDefToContext (success x₁) (networkDef x is hs os) = addDefinitionVarsToContext
      addVarsₙ (success x₁) (convertListToList⁺ is) hs (convertListToList⁺ os)

-- -- -- -- Checking assertions -- -- -- --
variableIndexInContext : (l : ScopeContext) → (vName : 𝐁.VariableName) →  Result (Fin (List.length (toList l)))
variableIndexInContext ctx name with any? (λ x → ⟦ x ⟧asString String.≟ ⟦ name ⟧asString) (toList ctx) -- (Any (λ x → x ≡ vName) (toList l))
... | yes p = success (index p)
... | no ¬p = error  

module _ (Γ : Context) where
  -- check arithmetic expressions
  checkExpressionₐᵣᵢₜₕ : ScopeContext → 𝐁.ArithExpr → 𝐕.ArithExpr Γ
  checkExpressionₐᵣᵢₜₕ Γ (varExpr x xs) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (doubleExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (sIntExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (intExpr x) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (negate a) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (plus as) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (minus a as) = {!!}
  checkExpressionₐᵣᵢₜₕ Γ (multiply as) = {!!}

  -- check boolean expressions
  postulate checkExpressionᵇᵒᵒˡ : ScopeContext → 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
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

  scopeCheckAssertions : ScopeContext → List⁺ 𝐁.Assertion → Result (List (𝐕.Property Γ))
  scopeCheckAssertions Γ (assert b ∷ tail₁) with checkExpressionᵇᵒᵒˡ Γ b
  ... | error = error
  ... | (success x) = {!!} 

-- Check Assertions from the constructed Scope Context
checkAssertions : List⁺ 𝐁.NetworkDefinition → List⁺ 𝐁.Assertion → Result 𝐕.Query
checkAssertions defs asserts with mkScopeContext defs
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

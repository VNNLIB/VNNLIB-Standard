module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Data.List as List
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕 hiding (Context; mkContext)


-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ (variableName name) ⟧asString = name

-- The result type
data Result (A : Set) : Set where
  error : Result A
  success : A → Result A


-- change to non-empty list using Data.List.Relation.Unary.Any

-- De Brujin's variable binding
data VariableBinding : Set where
  base : 𝐁.VariableName → VariableBinding
  -- change to function not pair
  rest : 𝐁.VariableName × VariableBinding → VariableBinding

getBindingVarName : VariableBinding → String
getBindingVarName (base x) =  ⟦ x ⟧asString
getBindingVarName (rest x) = ⟦ x .proj₁ ⟧asString

-- Check if the variable Binding variable name is equal to AST Variable Name
isVariableNameMatched : VariableBinding → 𝐁.VariableName → Bool
isVariableNameMatched varBind varName = ⟦ varName ⟧asString == getBindingVarName varBind

-- Context for Scope Checking
--> Scoping Context
Context : Set
Context = VariableBinding

-- Returns True/False if variable name is in the defined context
doesVariableExist : Context → 𝐁.VariableName → Bool
doesVariableExist (base x) varName = isVariableNameMatched (base x) varName
doesVariableExist (rest x) varName = isVariableNameMatched (rest x) varName ∨ isVariableNameMatched (x .proj₂) varName

-- Increment and return the De Brujin's index - assumes that the variable exists in the current context
lookUpDeBrujinIndex : Context → Bool → 𝐁.VariableName → ℕ
lookUpDeBrujinIndex (rest x) false varName = lookUpDeBrujinIndex (x .proj₂) (isVariableNameMatched (x .proj₂) (varName)) varName
lookUpDeBrujinIndex (rest x) true varName  = suc (lookUpDeBrujinIndex (x .proj₂) true varName)
lookUpDeBrujinIndex (base x) _ _ = zero -- defaults to 0 index

-- Create Context from network definitions
addToContext : Result Context → 𝐁.VariableName → Result Context
addToContext (success x) varName = if (doesVariableExist x varName) then error else success (rest (varName , x))
addToContext error varName = success (base varName)

isErrorContext : Result Context → Bool
isErrorContext error = true
isErrorContext (success x) = false

inputVars : 𝐁.InputDefinition → 𝐁.VariableName
inputVars (inputDef x e t) = x
inputVars (inputOnnxDef x₁ e t x₂) = x₁

hiddenVars : 𝐁.HiddenDefinition → 𝐁.VariableName
hiddenVars (hiddenDef x₁ e t x₂) = x₁

outputVars : 𝐁.OutputDefinition → 𝐁.VariableName
outputVars (outputDef x e t) = x
outputVars (outputOnnxDef x₁ e t x₂) = x₁

addVars : Result Context → List 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List 𝐁.OutputDefinition → Result Context
addVars Γ [] _ _ = error
addVars Γ (xᵢ ∷ is) _ [] = error
addVars Γ (xᵢ ∷ is) hs (xₒ ∷ os) = Γ₃
  where
    Γ₁ = foldl (λ ctx i → addToContext ctx (inputVars i)) Γ (xᵢ ∷ is)                                         -- input definitions to Γ
    Γ₂ = if isErrorContext Γ₁ then error else foldl (λ ctx h → addToContext ctx (hiddenVars h)) Γ₁ hs         -- then, hidden definitions to Γ
    Γ₃ = if isErrorContext Γ₂ then error else foldl (λ ctx o → addToContext ctx (outputVars o)) Γ₂ (xₒ ∷ os)  -- finally, output definitions to Γ

addNetworkDefToContext : Result Context → 𝐁.NetworkDefinition → Result Context
addNetworkDefToContext Γ (networkDef x is hs os) = addVars Γ is hs os

mkContext : List 𝐁.NetworkDefinition → Result Context
mkContext networkDefs = foldl (λ Γ n → addNetworkDefToContext Γ n) error networkDefs

postulate checkAssertions : Result Context → List 𝐁.Assertion → Result 𝐕.Query  

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ns []) = error
scopeCheck (vNNLibQuery [] (x ∷ as)) = error
scopeCheck (vNNLibQuery (x₁ ∷ ns) (x ∷ as)) = checkAssertions (mkContext (x₁ ∷ ns)) (x ∷ as)

module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Data.List as List
open import Data.Maybe using (Maybe; just; nothing)

open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕 hiding (Context; mkContext)

-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ (variableName name) ⟧asString = name

-- De Brujin's variable binding
data VariableBinding : Set where
  base : 𝐁.VariableName → VariableBinding
  rest : 𝐁.VariableName × VariableBinding → VariableBinding

getBindingVarName : VariableBinding → String
getBindingVarName (base x) =  ⟦ x ⟧asString
getBindingVarName (rest x) = ⟦ x .proj₁ ⟧asString

-- Check if the variable Binding variable name is equal to AST Variable Name
isVariableNameMatched : VariableBinding → 𝐁.VariableName → Bool
isVariableNameMatched varBind varName = ⟦ varName ⟧asString == getBindingVarName varBind

-- Context for Scope Checking
Context : Set
Context = VariableBinding

addToContext : Maybe Context → 𝐁.VariableName → Context
addToContext (just x) varName = rest (varName , x)
addToContext nothing varName = base varName

-- Returns True/False if variable name is in the defined context
doesVariableExist : Context → 𝐁.VariableName → Bool
doesVariableExist (base x) varName = isVariableNameMatched (base x) varName
doesVariableExist (rest x) varName = isVariableNameMatched (rest x) varName ∨ isVariableNameMatched (x .proj₂) varName

-- Increment and return the De Brujin's index
lookUpDeBrujinIndex : Context → Bool → 𝐁.VariableName → ℕ
lookUpDeBrujinIndex (rest x) false varName = lookUpDeBrujinIndex (x .proj₂) (isVariableNameMatched (x .proj₂) (varName)) varName
lookUpDeBrujinIndex (rest x) true varName  = suc (lookUpDeBrujinIndex (x .proj₂) true varName)
lookUpDeBrujinIndex (base x) _ _ = zero -- defaults to 0 index

addVarsᵢ : List 𝐁.InputDefinition → Maybe Context
addVarsᵢ [] = nothing
addVarsᵢ (inputDef x e t ∷ is) = just (addToContext (addVarsᵢ is) x)
addVarsᵢ (inputOnnxDef x₁ e t x₂ ∷ is) = just (addToContext (addVarsᵢ is) x₁)

addVarsₕ : List 𝐁.InputDefinition → List 𝐁.HiddenDefinition → Maybe Context
addVarsₕ [] _ = nothing
addVarsₕ (x ∷ is) hs = foldl
  (λ Γ → λ { (hiddenDef x₁ _ _ _) → just (addToContext Γ x₁) }) (addVarsᵢ (x ∷ is)) hs

addVarsₒ : List 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List 𝐁.OutputDefinition → Maybe Context
addVarsₒ [] _ _ = nothing
addVarsₒ (xᵢ ∷ is) _ [] = nothing
addVarsₒ (xᵢ ∷ is) hs (xₒ ∷ os) = foldl
  (λ Γ → λ { (outputDef x₁ _ _) → just (addToContext Γ x₁) ; (outputOnnxDef x₁ _ _ _) → just (addToContext Γ x₁) })
  (addVarsₕ (xᵢ ∷ is) hs) (xₒ ∷ os)

addNetworkDefToContext : Maybe Context → 𝐁.NetworkDefinition → Maybe Context
addNetworkDefToContext Γ (networkDef x is hs os) = addVarsₒ is hs os

mkContext : List 𝐁.NetworkDefinition → Maybe Context
mkContext [] = nothing
mkContext (x ∷ networkDefs) = foldl (λ Γ n → addNetworkDefToContext Γ n) nothing (x ∷ networkDefs)


-- scope checking
postulate scopeCheck : 𝐁.Query → 𝐕.Query

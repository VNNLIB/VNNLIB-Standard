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

addToContext : Context → 𝐁.VariableName → Context
addToContext ctx varName = rest (varName , ctx)

-- Returns True/False if variable name is in the defined context
doesVariableExist : Context → 𝐁.VariableName → Bool
doesVariableExist (base x) varName = isVariableNameMatched (base x) varName
doesVariableExist (rest x) varName = isVariableNameMatched (rest x) varName ∨ isVariableNameMatched (x .proj₂) varName

-- Increment and return the De Brujin's index - assumes that the variable exists in the context
lookUpDeBrujinIndex : Context → Bool → 𝐁.VariableName → ℕ
lookUpDeBrujinIndex (rest x) false varName = lookUpDeBrujinIndex (x .proj₂) (isVariableNameMatched (x .proj₂) (varName)) varName
lookUpDeBrujinIndex (rest x) true varName  = suc (lookUpDeBrujinIndex (x .proj₂) true varName)
lookUpDeBrujinIndex (base x) _ _ = zero -- defaults to 0 index



addVars₃ : List 𝐁.InputDefinition → Context
addVars₃ is = {!!}

addVars₂ : List 𝐁.InputDefinition → List 𝐁.HiddenDefinition → Context
addVars₂ is hs = foldl {!!} (addVars₃ is) hs

addVars₁ : List 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List 𝐁.OutputDefinition → Context
addVars₁ is hs os = {!!} 


addNetworkDefToContext : 𝐁.NetworkDefinition → Context
addNetworkDefToContext (networkDef x is hs os)  = addVars₁ is hs os

mkContext : List 𝐁.NetworkDefinition → Context
mkContext [] = {!!}
mkContext (x ∷ networkDefs) = {!!}


-- scope checking
postulate scopeCheck : 𝐁.Query → 𝐕.Query

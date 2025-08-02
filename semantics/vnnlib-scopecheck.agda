module vnnlib-scopecheck where

open import Data.Nat as ℕ
open import Data.Product as Product
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Data.Fin as Fin
open import Data.List as List hiding (lookup; foldl)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.NonEmpty as List⁺
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕 hiding (Context; mkContext)


-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ (variableName name) ⟧asString = name

-- The result type
data Result (A : Set) : Set where
  error : Result A
  success : A → Result A

convertMaybeToResult : {A : Set} → Maybe A → Result A
convertMaybeToResult (just x) = success x
convertMaybeToResult nothing = error

convertListToNonEmptyList : {A : Set} → List A → Result (List⁺ A)
convertListToNonEmptyList lst = convertMaybeToResult (fromList lst)

-- Context for scope checking
ScopeContext : Set
ScopeContext = List⁺ (𝐁.VariableName) -- × with 𝐁.TensorShape

-- Returns True/False if variable name is in the defined context
doesVariableNameExist : ScopeContext → 𝐁.VariableName → Bool
doesVariableNameExist(head₁ ∷ []) name = ⟦ head₁ ⟧asString == ⟦ name ⟧asString
doesVariableNameExist (head₁ ∷ x ∷ tail₁) name = false ∨ (⟦ x ⟧asString == ⟦ name ⟧asString) ∨ (doesVariableNameExist (head₁ ∷ tail₁) name)

-- Takes the ScopeContext and a variable Name, and produces an `Any Bool List` with `here true` where the Scope Context == variableName
variableNameInContext : (l : ScopeContext) → 𝐁.VariableName → Result (Any (λ z → Bool) (toList l))
variableNameInContext (head₁ ∷ []) name = if doesVariableNameExist (head₁ ∷ []) name then success (here true) else error
variableNameInContext (head₁ ∷ x ∷ tail₁) name = if doesVariableNameExist (x ∷ []) name then {!!} else {!!}
  where
    varHead : ScopeContext → 𝐁.VariableName → Bool
    varHead ctx vname = doesVariableNameExist ctx vname

-- Assumes that the variable name is already in context
getDeBrujin'sIndex : {l : ScopeContext} → Any (λ z → Bool) (toList l) → Fin (List.length (toList l))
getDeBrujin'sIndex actx = index actx


-- Create Context from network definitions
-- -- The first addition to the scope context - the only instance where an error ScopeContext can be built on
addToContext₁ : Result ScopeContext → 𝐁.VariableName → Result ScopeContext
addToContext₁ (success x) varName = success (varName ∷⁺ x)
addToContext₁ error varName = success (varName ∷ [])
-- -- Concequent additions
addToContextₙ : Result ScopeContext → 𝐁.VariableName → Result ScopeContext
addToContextₙ error varName = error
addToContextₙ (success x) varName = if doesVariableNameExist x varName then error else success (varName ∷⁺ x)

-- Get variable Names
inputVars : 𝐁.InputDefinition → 𝐁.VariableName
inputVars (inputDef x e t) = x
inputVars (inputOnnxDef x₁ e t x₂) = x₁

hiddenVars : 𝐁.HiddenDefinition → 𝐁.VariableName
hiddenVars (hiddenDef x₁ e t x₂) = x₁

outputVars : 𝐁.OutputDefinition → 𝐁.VariableName
outputVars (outputDef x e t) = x
outputVars (outputOnnxDef x₁ e t x₂) = x₁


-- Utilized for the first network definition, to first construct the context
addVars₁ : Result ScopeContext → List⁺ 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List⁺ 𝐁.OutputDefinition → Result ScopeContext
addVars₁ Γ is hs os = Γ₃ 
  where
    Γ₁ = foldl (λ ctx i → addToContextₙ ctx (inputVars i)) (λ i → addToContext₁ Γ (inputVars i)) is    -- input definitions to Γ
    Γ₂ = List.foldl (λ ctx h → addToContextₙ ctx (hiddenVars h)) Γ₁ hs                                 -- then, hidden definitions to Γ
    Γ₃ = foldl (λ ctx o → addToContextₙ ctx (outputVars o)) (λ o → addToContextₙ Γ (outputVars o)) os  -- finally, output definitions to Γ


addVarsₙ : Result ScopeContext → List⁺ 𝐁.InputDefinition → List 𝐁.HiddenDefinition → List⁺ 𝐁.OutputDefinition → Result ScopeContext
addVarsₙ Γ is hs os = Γ₃
  where
    Γ₁ = foldl (λ ctx i → addToContextₙ ctx (inputVars i)) (λ i → addToContextₙ Γ (inputVars i)) is    -- input definitions to Γ
    Γ₂ = List.foldl (λ ctx h → addToContextₙ ctx (hiddenVars h)) Γ₁ hs                                 -- then, hidden definitions to Γ
    Γ₃ = foldl (λ ctx o → addToContextₙ ctx (outputVars o)) (λ o → addToContextₙ Γ (outputVars o)) os  -- finally, output definitions to Γ

-- Convert the input and output definitions from List to List⁺
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
    addNetworkDefToContext₁ : 𝐁.NetworkDefinition → Result ScopeContext
    addNetworkDefToContext₁ (networkDef x is hs os) = addDefinitionVarsToContext
      addVars₁ error ((λ lₙ → convertListToNonEmptyList lₙ) is) hs ((λ lₙ → convertListToNonEmptyList lₙ) os)
      
    addNetworkDefToContext : Result ScopeContext → 𝐁.NetworkDefinition → Result ScopeContext
    addNetworkDefToContext error (networkDef x is hs os) = error
    addNetworkDefToContext (success x₁) (networkDef x is hs os) = addDefinitionVarsToContext
      addVarsₙ (success x₁) ((λ lₙ → convertListToNonEmptyList lₙ) is) hs ((λ lₙ → convertListToNonEmptyList lₙ) os)
    
      
postulate checkAssertions : Result ScopeContext → List⁺ 𝐁.Assertion → Result 𝐕.Query  

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ns as) = queries⁺ ((λ lₙ → convertListToNonEmptyList lₙ) ns) ((λ lₙ → convertListToNonEmptyList lₙ) as)
  where
    queries⁺ : Result (List⁺ 𝐁.NetworkDefinition) → Result (List⁺ 𝐁.Assertion) → Result 𝐕.Query
    queries⁺ error net = error
    queries⁺ (success x) error = error
    queries⁺ (success x) (success x₁) = checkAssertions (mkScopeContext x) x₁

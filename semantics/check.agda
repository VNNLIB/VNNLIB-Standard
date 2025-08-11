module check where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Relation.Binary.PropositionalEquality
open import Data.Fin as Fin
open import Data.Nat as ℕ
open import vnnlib-syntax as 𝐕
open import Syntax.AST as 𝐁 hiding (String)
open import Data.List.Relation.Unary.Any as RUAny
open import Relation.Nullary

open import tensor as 𝐓 using (TensorShape)
open import syntax-utils
open import types-utils

-- Context for both scope and type checking
data VariableBinding : Set where
  var : 𝐕.VariableName → 𝐓.TensorShape → 𝐕.ElementType → VariableBinding

getVariableNameᴮ : VariableBinding → 𝐁.VariableName
getVariableNameᴮ (var (SVariableName x) x₁ x₂) = variableName x

getTensorShape : VariableBinding → 𝐓.TensorShape
getTensorShape (var x x₁ x₂) = x₁

record NetworkBinding : Set where
  constructor
    networkBinding
  field
    inputs : List⁺ VariableBinding
    outputs : List⁺ VariableBinding

CheckContext : Set
CheckContext = List⁺ (NetworkBinding)


-- get DeBrujin's index from context
open NetworkBinding

variableIndexInNetworkᵢₙₚᵤₜ : (n : NetworkBinding) → (varName : 𝐁.VariableName) → Result (Fin (List.length (toList (inputs n))))
variableIndexInNetworkᵢₙₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asString String.≟ ⟦ getVariableNameᴮ x ⟧asString) (toList (inputs Ν)) -- Any (λ x → getVariableName x ≡ convertVariableName(varName)) (toList (inputs n))
... | yes p = success (index p)
... | no ¬p = error

variableIndexInNetworkₒᵤₜₚᵤₜ : (n : NetworkBinding) → (varName : 𝐁.VariableName) → Result (Fin (List.length (toList (outputs n))))
variableIndexInNetworkₒᵤₜₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asString String.≟ ⟦ getVariableNameᴮ x ⟧asString) (toList (outputs Ν))
... | yes p = success (index p)
... | no ¬p = error

checkNetworkIndex : (varName : 𝐁.VariableName) → (n : NetworkBinding) → Result Bool -- the Bool is placeholder enum type
checkNetworkIndex varName Ν with variableIndexInNetworkᵢₙₚᵤₜ Ν varName
... | success x = success (true)
... | error with variableIndexInNetworkₒᵤₜₚᵤₜ Ν varName
... | success x = success (true)
... | error = error

isResultSuccess : Result Bool → Bool
isResultSuccess error = false
isResultSuccess (success _) = true

postulate variableNetworkIndex : (l : CheckContext) → (varName : 𝐁.VariableName) → Result (Fin (List.length (toList l)))
-- variableNetworkIndex Γ varName with any? (λ x → isResultSuccess x Bool.≟ true) result
--  where
--    contextₗ = toList Γ
--    result : List (Result Bool)
--    result = List.map (checkNetworkIndex varName) (toList Γ)
--... | yes p = success ({! ?!})
--... | no ¬p = error


-- Make CheckContext from 𝐁.Network Definitions
postulate mkNetworkInputs : List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)

postulate mkNetworkOutputs : List⁺ 𝐁.OutputDefinition → Result (List⁺ VariableBinding)

mkNetworkContext : 𝐁.NetworkDefinition → Result (NetworkBinding)
mkNetworkContext (networkDef _ is _ os) with convertListToList⁺ is -- non empty input definitions
... | error = error
... | success is with convertListToList⁺ os -- non empty output definitions
... | error = error
... | success os with mkNetworkInputs is    -- add input definitions to variable definition
... | error = error
... | success varsᵢ with mkNetworkOutputs os -- add output definitions
... | error = error
... | success varsₒ = success (networkBinding varsᵢ varsₒ)


postulate mkCheckContext : List⁺ 𝐁.NetworkDefinition → Result CheckContext
-- mkCheckContext networkDefs = {!!} -- List⁺.map mkNetworkContext networkDefs

-- derive the 𝐕.Context from the constructed ScopeContext
convertCheckContext : CheckContext → Context
convertCheckContext Γₛ = List.foldl
  (λ z → λ {(networkBinding inputs₁ outputs₁) → networkType (List.map getTensorShape (toList inputs₁)) (List.map getTensorShape (toList outputs₁)) ∷ z }) [] (toList Γₛ)

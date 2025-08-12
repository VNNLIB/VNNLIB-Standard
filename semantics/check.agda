module check where

open import Data.List as List
open import Data.List.Properties using (length-map)
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

toVariableBindingᵢ : 𝐁.InputDefinition → VariableBinding
toVariableBindingᵢ (inputDef x e t) = var (convertVariableName x) (convertTensorShape t) (convertElementType e)
toVariableBindingᵢ (inputOnnxDef x₁ e t x₂) = var (convertVariableName x₁) (convertTensorShape t) (convertElementType e)

toVariableBindingₒ : 𝐁.OutputDefinition → VariableBinding
toVariableBindingₒ (outputDef x e t) = var (convertVariableName x) (convertTensorShape t) (convertElementType e)
toVariableBindingₒ (outputOnnxDef x₁ e t x₂) = var (convertVariableName x₁) (convertTensorShape t) (convertElementType e)

isVariableNameInVariableBinding : 𝐁.VariableName → List⁺ VariableBinding → Bool
isVariableNameInVariableBinding varName vars = List.foldl (λ bool var₁ → bool ∨ (⟦ varName ⟧asString == ⟦ getVariableNameᴮ var₁ ⟧asString)) false (toList vars)

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

-- the network index is derived if the variable is in its inputs or outputs
checkNetworkIndex : (varName : 𝐁.VariableName) → (n : NetworkBinding) → Result Bool -- the Bool is placeholder enum type
checkNetworkIndex varName Ν with variableIndexInNetworkᵢₙₚᵤₜ Ν varName
... | success x = success (true)
... | error with variableIndexInNetworkₒᵤₜₚᵤₜ Ν varName
... | success x = success (true)
... | error = error

isResultSuccess : Result Bool → Bool
isResultSuccess error = false
isResultSuccess (success _) = true

variableNetworkIndex : (varName : 𝐁.VariableName) → (l : CheckContext) → Result (Fin (List.length (toList l)))
variableNetworkIndex varName Γ with any? (λ x → isResultSuccess x Bool.≟ true) (List.map (checkNetworkIndex varName) (toList Γ))
... | yes p = success (subst Fin equal-length (index p))
  where
    -- proof that the length of the mapped results list is equivalent
    equal-length : List.length (List.map (checkNetworkIndex varName) (toList Γ)) ≡ List.length (toList Γ)
    equal-length = length-map (checkNetworkIndex varName) (toList Γ)
... | no ¬p = error


-- Check the current context and interatively built Variable Binding to determine if the adding variable name is unique
isVariableNameUnique : 𝐁.VariableName → CheckContext → List VariableBinding → Bool
isVariableNameUnique varName Γ vars with variableNetworkIndex varName Γ -- checking for the repeated name in the context
... | success _ = false
... | error with convertListToList⁺ vars
... | error = true
... | success vars⁺ = not (isVariableNameInVariableBinding varName vars⁺) -- checking if variable name is unique

-- Make CheckContext from 𝐁.Network Definitions
----------- Add network Inputs -----------------
mkNetworkInputs₁ : List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)
mkNetworkInputs₁ is = List⁺.foldl addInputVarₙ addInputVar₁ is
  where
    addInputVar₁ : 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVar₁ i = success (List⁺.[ toVariableBindingᵢ i ])
    
    addInputVarₙ : Result (List⁺ VariableBinding) → 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVarₙ error i = error
    addInputVarₙ (success n) i with inputVars i
    ... | varName with isVariableNameInVariableBinding varName n -- checking for the repeated name in the iteratively built inputVars list
    ... | true = error
    ... | false = success(toVariableBindingᵢ i ∷⁺ n)

mkNetworkInputsₙ : CheckContext → List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)
mkNetworkInputsₙ Γ is = List⁺.foldl addInputVarₙ addInputVar₁ is
  where
    addInputVar₁ : 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVar₁ i with inputVars i
    ... | varNameᵢ with isVariableNameUnique varNameᵢ Γ []
    ... | false = error
    ... | true = success (List⁺.[ toVariableBindingᵢ i ])
    
    addInputVarₙ : Result (List⁺ VariableBinding) → 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVarₙ error i = error
    addInputVarₙ (success n) i with inputVars i
    ... | varName with isVariableNameUnique varName Γ (toList n) -- checking for the repeated name in the iteratively built inputVars list
    ... | false = error
    ... | true = success (toVariableBindingᵢ i ∷⁺ n)

------------- Add network outputs ----------------

mkNetworkOutputs₁ : List⁺ VariableBinding → List⁺ 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
mkNetworkOutputs₁ varsᵢ os = List⁺.foldl addOutputVarₙ addOutputVar₁ os
  where
    addOutputVar₁ : 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVar₁ o with outputVars o
    ... | varName with isVariableNameInVariableBinding varName varsᵢ -- checking if variable name is in the input vars
    ... | true = error
    ... | false = success (List⁺.[ toVariableBindingₒ o ])
    
    addOutputVarₙ : Result (List⁺ VariableBinding) → 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVarₙ error _ = error
    addOutputVarₙ (success n) o with outputVars o
    ... | varName with isVariableNameInVariableBinding varName varsᵢ -- checking if variable name is in the input vars
    ... | true = error
    ... | false with isVariableNameInVariableBinding varName n -- checking for the repeated name in the iteratively built outputVars list
    ... | true = error
    ... | false = success(toVariableBindingₒ o ∷⁺ n)

mkNetworkOutputsₙ : CheckContext → List⁺ VariableBinding → List⁺ 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
mkNetworkOutputsₙ Γ varsᵢ os = List⁺.foldl addOutputVarₙ addOutputVar₁ os
  where
    addOutputVar₁ : 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVar₁ o with outputVars o
    ... | varName with isVariableNameUnique varName Γ (toList varsᵢ) -- checking if variable name is in the input vars
    ... | false = error
    ... | true = success (List⁺.[ toVariableBindingₒ o ])
    
    addOutputVarₙ : Result (List⁺ VariableBinding) → 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVarₙ error _ = error
    addOutputVarₙ (success n) o with outputVars o
    ... | varName with isVariableNameUnique varName Γ (toList varsᵢ) -- checking if variable name is in the input vars
    ... | false = error
    ... | true with isVariableNameUnique varName Γ (toList n) -- checking for the repeated name in the iteratively built outputVars list
    ... | false = error
    ... | true = success(toVariableBindingₒ o ∷⁺ n)

----------- Add networks to context -----------
mkNetworkContext₁ : List⁺ 𝐁.InputDefinition → List⁺ 𝐁.OutputDefinition → Result (NetworkBinding)
mkNetworkContext₁ is os with mkNetworkInputs₁ is  -- add input definitions to variable definition
... | error = error
... | success varsᵢ with mkNetworkOutputs₁ varsᵢ os -- add output definitions
... | error = error
... | success varsₒ = success (networkBinding varsᵢ varsₒ)

mkNetworkContextₙ : CheckContext → List⁺ 𝐁.InputDefinition → List⁺ 𝐁.OutputDefinition → Result (NetworkBinding)
mkNetworkContextₙ Γ is os with mkNetworkInputsₙ Γ is    -- add input definitions to variable definition
... | error = error
... | success varsᵢ with mkNetworkOutputsₙ Γ varsᵢ os -- add output definitions
... | error = error
... | success varsₒ = success (networkBinding varsᵢ varsₒ)

------------ Create the Check context -----------
mkCheckContext : List⁺ 𝐁.NetworkDefinition → Result CheckContext
mkCheckContext networkDefs = List⁺.foldl networkₙ network₁ networkDefs
  where
    network₁ : 𝐁.NetworkDefinition → Result CheckContext
    network₁ netDef with convertListToList⁺ (getInputDefs netDef)
    ... | error = error
    ... | success is with convertListToList⁺ (getOutputDefs netDef)
    ... | error = error
    ... | success os with mkNetworkContext₁ is os
    ... | error = error
    ... | success x = success (List⁺.[ x ])
    networkₙ : Result CheckContext → 𝐁.NetworkDefinition → Result CheckContext
    networkₙ error netDef = error
    networkₙ (success Γ) netDef with convertListToList⁺ (getInputDefs netDef)
    ... | error = error
    ... | success is with convertListToList⁺ (getOutputDefs netDef)
    ... | error = error
    ... | success os with mkNetworkContextₙ Γ is os
    ... | error = error
    ... | success x = success ( x ∷⁺ Γ )
    

-- derive the 𝐕.Context from the constructed CheckContext
convertCheckContext : CheckContext → Context
convertCheckContext Γᶜ = List.foldl
  (λ z → λ {(networkBinding inputs₁ outputs₁) → networkType (List.map getTensorShape (toList inputs₁)) (List.map getTensorShape (toList outputs₁)) ∷ z }) [] (toList Γᶜ)

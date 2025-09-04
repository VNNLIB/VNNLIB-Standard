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
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (_∘_)

open import tensor as 𝐓 using (TensorShape)
open import syntax-utils
open import types-utils
open import vnnlib-types as 𝐄

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

-- Context for both scope and type checking
data VariableBinding : Set where
  var : 𝐕.VariableName → 𝐓.TensorShape → 𝐄.ElementType → VariableBinding

getVariableNameᴮ : VariableBinding → 𝐁.VariableName
getVariableNameᴮ (var (SVariableName x) x₁ x₂) = variableName x

getTensorShape : VariableBinding → 𝐓.TensorShape
getTensorShape (var x x₁ x₂) = x₁

fromVariableBindingᵢ : VariableBinding → 𝐕.InputDefinition
fromVariableBindingᵢ (var x x₁ x₂) = declareInput x x₂ x₁

fromVariableBindingₒ : VariableBinding → 𝐕.OutputDefinition
fromVariableBindingₒ (var x x₁ x₂) = declareOutput x x₂ x₁


toVariableBindingᵢ : 𝐁.InputDefinition → VariableBinding
toVariableBindingᵢ (inputDef x e t) = var (convertVariableName x) (convertTensorShape t) (convertElementType e)
toVariableBindingᵢ (inputOnnxDef x₁ e t x₂) = var (convertVariableName x₁) (convertTensorShape t) (convertElementType e)

toVariableBindingₒ : 𝐁.OutputDefinition → VariableBinding
toVariableBindingₒ (outputDef x e t) = var (convertVariableName x) (convertTensorShape t) (convertElementType e)
toVariableBindingₒ (outputOnnxDef x₁ e t x₂) = var (convertVariableName x₁) (convertTensorShape t) (convertElementType e)


record NetworkBinding : Set where
  constructor
    networkBinding
  field
    inputs : List⁺ VariableBinding
    outputs : List⁺ VariableBinding

CheckContextPair : Set
CheckContextPair = NetworkBinding × 𝐕.NetworkDefinition

CheckContext : Set
CheckContext = List (CheckContextPair)

convertNetworkBindingToDef : 𝐕.VariableName → NetworkBinding → 𝐕.NetworkDefinition
convertNetworkBindingToDef networkName (networkBinding inputs₁ outputs₁) = declareNetwork networkName (List.map fromVariableBindingᵢ (toList inputs₁)) (List.map fromVariableBindingₒ (toList outputs₁))


-- get DeBrujin's index from context
open NetworkBinding

variableIndexInNetworkᵢₙₚᵤₜ : (n : NetworkBinding) → (varName : 𝐁.VariableName) → Result (Fin (List.length (toList (inputs n))))
variableIndexInNetworkᵢₙₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asString String.≟ ⟦ getVariableNameᴮ x ⟧asString) (toList (inputs Ν))
... | yes p = success (index p)
... | no ¬p = error "Variable Name not in inputs"

variableIndexInNetworkₒᵤₜₚᵤₜ : (n : NetworkBinding) → (varName : 𝐁.VariableName) → Result (Fin (List.length (toList (outputs n))))
variableIndexInNetworkₒᵤₜₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asString String.≟ ⟦ getVariableNameᴮ x ⟧asString) (toList (outputs Ν))
... | yes p = success (index p)
... | no ¬p = error "Variable Input Name must be unique"

-- the network index is derived if the variable is in its inputs or outputs
checkNetworkIndex : (varName : 𝐁.VariableName) → (n : NetworkBinding) → Result Bool -- the Bool is placeholder enum type
checkNetworkIndex varName Ν with variableIndexInNetworkᵢₙₚᵤₜ Ν varName
... | success x = success (true)
... | error _ with variableIndexInNetworkₒᵤₜₚᵤₜ Ν varName
... | success x = success (true)
... | error _ = error "Variable Name in network Binding not unique"

isResultSuccess : Result Bool → Bool
isResultSuccess (error _) = false
isResultSuccess (success _) = true

getNetworkBindings : CheckContext → List NetworkBinding
getNetworkBindings Γ = List.map proj₁ Γ

variableNetworkIndex : (varName : 𝐁.VariableName) → (l : CheckContext) → Result (Fin (List.length l))
variableNetworkIndex varName Γ with any? (λ x → isResultSuccess x Bool.≟ true) (List.map (checkNetworkIndex varName ∘ proj₁) Γ)
... | yes p = success (subst Fin equal-length (index p))
  where
    equal-length : List.length (List.map (checkNetworkIndex varName ∘ proj₁) Γ) ≡ List.length Γ
    equal-length = length-map (checkNetworkIndex varName ∘ proj₁) Γ
... | no ¬p = error ""

isVariableNameInVariableBinding : 𝐁.VariableName → List⁺ VariableBinding → Bool
isVariableNameInVariableBinding varName vars with any? (λ x → ⟦ varName ⟧asString String.≟ ⟦ getVariableNameᴮ x ⟧asString) (toList vars)
... | yes _ = true
... | no _ = false


-- Check the current context and interatively built Variable Binding to determine if the adding variable name is unique
isVariableNameUnique : 𝐁.VariableName → CheckContext → List VariableBinding → Bool
isVariableNameUnique varName Γ vars with variableNetworkIndex varName Γ -- checking for the repeated name in the context
... | success x = false
... | error _ with convertListToList⁺ vars
... | error _ = true
... | success vars⁺ = not (isVariableNameInVariableBinding varName vars⁺) -- checking if variable name is unique

-- Make CheckContext from 𝐁.Network Definitions
----------- Add network Inputs -----------------
mkNetworkInputs₁ : List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)
mkNetworkInputs₁ is = List⁺.foldl addInputVarₙ addInputVar₁ is
  where
    addInputVar₁ : 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVar₁ i = success (List⁺.[ toVariableBindingᵢ i ])
    
    addInputVarₙ : Result (List⁺ VariableBinding) → 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVarₙ (error _) i = error ""
    addInputVarₙ (success n) i with inputVars i
    ... | varName with isVariableNameInVariableBinding varName n -- checking for the repeated name in the iteratively built inputVars list
    ... | true = error ""
    ... | false = success(toVariableBindingᵢ i ∷⁺ n)

mkNetworkInputsₙ : CheckContext → List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)
mkNetworkInputsₙ Γ is = List⁺.foldl addInputVarₙ addInputVar₁ is
  where
    addInputVar₁ : 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVar₁ i with inputVars i
    ... | varNameᵢ with isVariableNameUnique varNameᵢ Γ []
    ... | false = error ""
    ... | true = success (List⁺.[ toVariableBindingᵢ i ])
    
    addInputVarₙ : Result (List⁺ VariableBinding) → 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVarₙ (error _) i = error ""
    addInputVarₙ (success n) i with inputVars i
    ... | varName with isVariableNameUnique varName Γ (toList n) -- checking for the repeated name in the iteratively built inputVars list
    ... | false = error ""
    ... | true = success (toVariableBindingᵢ i ∷⁺ n)

------------- Add network outputs ----------------

mkNetworkOutputs₁ : List⁺ VariableBinding → List⁺ 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
mkNetworkOutputs₁ varsᵢ os = List⁺.foldl addOutputVarₙ addOutputVar₁ os
  where
    addOutputVar₁ : 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVar₁ o with outputVars o
    ... | varName with isVariableNameInVariableBinding varName varsᵢ -- checking if variable name is in the input vars
    ... | true = error ""
    ... | false = success (List⁺.[ toVariableBindingₒ o ])
    
    addOutputVarₙ : Result (List⁺ VariableBinding) → 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVarₙ (error _) _ = error ""
    addOutputVarₙ (success n) o with outputVars o
    ... | varName with isVariableNameInVariableBinding varName varsᵢ -- checking if variable name is in the input vars
    ... | true = error ""
    ... | false with isVariableNameInVariableBinding varName n -- checking for the repeated name in the iteratively built outputVars list
    ... | true = error ""
    ... | false = success(toVariableBindingₒ o ∷⁺ n)

mkNetworkOutputsₙ : CheckContext → List⁺ VariableBinding → List⁺ 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
mkNetworkOutputsₙ Γ varsᵢ os = List⁺.foldl addOutputVarₙ addOutputVar₁ os
  where
    addOutputVar₁ : 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVar₁ o with outputVars o
    ... | varName with isVariableNameUnique varName Γ (toList varsᵢ) -- checking if variable name is in the input vars
    ... | false = error ""
    ... | true = success (List⁺.[ toVariableBindingₒ o ])
    
    addOutputVarₙ : Result (List⁺ VariableBinding) → 𝐁.OutputDefinition → Result (List⁺ VariableBinding)
    addOutputVarₙ (error _) _ = error ""
    addOutputVarₙ (success n) o with outputVars o
    ... | varName with isVariableNameUnique varName Γ (toList varsᵢ) -- checking if variable name is in the input vars
    ... | false = error ""
    ... | true with isVariableNameUnique varName Γ (toList n) -- checking for the repeated name in the iteratively built outputVars list
    ... | false = error ""
    ... | true = success(toVariableBindingₒ o ∷⁺ n)

----------- Add networks to context -----------
mkNetworkContext₁ : List⁺ 𝐁.InputDefinition → List⁺ 𝐁.OutputDefinition → Result (NetworkBinding)
mkNetworkContext₁ is os with mkNetworkInputs₁ is  -- add input definitions to variable definition
... | error _ = error ""
... | success varsᵢ with mkNetworkOutputs₁ varsᵢ os -- add output definitions
... | error _ = error ""
... | success varsₒ = success (networkBinding varsᵢ varsₒ)

mkNetworkContextₙ : CheckContext → List⁺ 𝐁.InputDefinition → List⁺ 𝐁.OutputDefinition → Result (NetworkBinding)
mkNetworkContextₙ Γ is os with mkNetworkInputsₙ Γ is    -- add input definitions to variable definition
... | error _ = error ""
... | success varsᵢ with mkNetworkOutputsₙ Γ varsᵢ os -- add output definitions
... | error _ = error ""
... | success varsₒ = success (networkBinding varsᵢ varsₒ)

------------ Create the Check context -----------
mkCheckContext : List 𝐁.NetworkDefinition → Result CheckContext
mkCheckContext networkDefs = List.foldl networkₙ (success []) networkDefs
  where
    networkₙ : Result CheckContext → 𝐁.NetworkDefinition → Result CheckContext
    networkₙ (error _) netDef = error ""
    networkₙ (success Γ) netDef with convertListToList⁺ (getInputDefs netDef)
    ... | error _ = error ""
    ... | success is with convertListToList⁺ (getOutputDefs netDef)
    ... | error _ = error ""
    ... | success os with mkNetworkContextₙ Γ is os
    ... | error _ = error ""
    ... | success x = success ( (x , convertNetworkBindingToDef (convertVariableName (getNetworkName netDef)) x) ∷ Γ)


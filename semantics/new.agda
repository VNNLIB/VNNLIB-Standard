module new where

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

getVariableName : VariableBinding → 𝐕.VariableName
getVariableName (var x _ _) = x


toVariableBindingᵢ : 𝐕.InputDefinition → VariableBinding
toVariableBindingᵢ (declareInput x x₁ x₂) = var x x₂ x₁

toVariableBindingₒ : 𝐕.OutputDefinition → VariableBinding
toVariableBindingₒ (declareOutput x x₁ x₂) = var x x₂ x₁

fromVariableBindingᵢ : VariableBinding → 𝐕.InputDefinition
fromVariableBindingᵢ (var x x₁ x₂) = declareInput x x₂ x₁

fromVariableBindingₒ : VariableBinding → 𝐕.OutputDefinition
fromVariableBindingₒ (var x x₁ x₂) = declareOutput x x₂ x₁


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


-- Every network Definition must have non empty lists of inputs and outputs
convertNetworkDefToBinding : 𝐕.NetworkDefinition → Result (NetworkBinding)
convertNetworkDefToBinding (declareNetwork x x₁ x₂) with convertListToList⁺ x₁
... | error = error
... | success x₁ with convertListToList⁺ x₂
... |    error = error
... |    success x₂ = success (networkBinding (List⁺.map toVariableBindingᵢ x₁) (List⁺.map toVariableBindingₒ x₂))


convertNetworkBindingToDef : NetworkBinding → 𝐕.NetworkDefinition
convertNetworkBindingToDef (networkBinding inputs₁ outputs₁) = declareNetwork (SVariableName "") (List.map fromVariableBindingᵢ (toList inputs₁)) (List.map fromVariableBindingₒ (toList outputs₁))

-- convertNetworkDefToContext : List⁺ 𝐕.NetworkDefinition → 

mkNetworkInputs₁ : List⁺ 𝐁.InputDefinition → Result (List⁺ VariableBinding)
mkNetworkInputs₁ is = List⁺.foldl addInputVarₙ (λ i → success (List⁺.[ toVariableBindingᵢ (convertInputDefinition i) ])) is
  where
    addInputVarₙ : Result (List⁺ VariableBinding) → 𝐁.InputDefinition → Result (List⁺ VariableBinding)
    addInputVarₙ error i = error
    addInputVarₙ (success n) i with inputVars i
    ... | varName with any? (λ x → ⟦ varName ⟧asString String.≟ ⟦ x ⟧asString) (List.map {!!} (toList n)) -- checking for the repeated name in the iteratively built inputVars list
    ... | yes p = success ({!!})
    ... | no ¬p = error
--    ... | y = error
--    ... | false = success(toVariableBindingᵢ i ∷⁺ n)


checkNetworkDefinition₁ : 𝐕.NetworkDefinition → Result 𝐕.NetworkDefinition
checkNetworkDefinition₁ n with convertNetworkDefToBinding n
... | error = error
... | success (networkBinding inputs₁ outputs₁) = {!!}


checkNetworkDefinition : List⁺ 𝐕.NetworkDefinition → 𝐕.NetworkDefinition → Result (List⁺ 𝐕.NetworkDefinition)
checkNetworkDefinition networkDefs newDef = {!!}



convertDefsToContext : List⁺ 𝐕.NetworkDefinition → Result (CheckContext)
convertDefsToContext networkDefs = error
    
mkScopeContextFromDefs : List⁺ 𝐁.NetworkDefinition → Result (List⁺ 𝐕.NetworkDefinition)
mkScopeContextFromDefs networkDefs = List⁺.foldl checkNetworkDefs (λ z → success ( List⁺.[ convertNetworkDefinition z ] )) networkDefs
  where
    checkNetworkDefs : Result (List⁺ 𝐕.NetworkDefinition) → 𝐁.NetworkDefinition → Result (List⁺ 𝐕.NetworkDefinition)
    checkNetworkDefs error _ = error
    checkNetworkDefs (success defs) newDef = {!!}


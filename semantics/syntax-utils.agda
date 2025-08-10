module syntax-utils where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.String as String hiding (toList)
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import Data.Nat as ℕ
open import Data.Integer as ℤ using (∣_∣)

-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ (variableName name) ⟧asString = name

convertElementType : 𝐁.ElementType → 𝐕.ElementType
convertElementType genericElementType = real
convertElementType elementTypeF16 = float16
convertElementType elementTypeF32 = float32
convertElementType elementTypeF64 = float64
convertElementType elementTypeBF16 = bfloat16 
convertElementType elementTypeF8E4M3FN = float8e4m3fn
convertElementType elementTypeF8E5M2 = float8e5m2 
convertElementType elementTypeF8E4M3FNUZ = float8e4m3fnuz
convertElementType elementTypeF8E5M2FNUZ = float8e5m2fnuz
convertElementType elementTypeF4E2M1 = float4e2m1
convertElementType elementTypeI8 = int8
convertElementType elementTypeI16 = int16
convertElementType elementTypeI32 = int32
convertElementType elementTypeI64 = int64
convertElementType elementTypeU8 = uint8
convertElementType elementTypeU16 = uint16
convertElementType elementTypeU32 = uint32
convertElementType elementTypeU64 = uint64
convertElementType elementTypeC64 = complex64
convertElementType elementTypeC128 = complex128
convertElementType elementTypeBool = boolType
convertElementType elementTypeString = stringType

convertVariableName : 𝐁.VariableName → 𝐕.VariableName
convertVariableName (variableName x) = SVariableName x

postulate convertTensorShape : 𝐁.TensorShape → List ℕ
-- convertTensorShape scalarDims = []
-- convertTensorShape (tensorDims []) = []
-- convertTensorShape (tensorDims (x ∷ xs)) =  ∣ {!!} ∣ ∷ convertTensorShape (tensorDims xs) 

convertInputDefinition : 𝐁.InputDefinition → 𝐕.InputDefinition
convertInputDefinition (inputDef x e t) = declareInput (SVariableName ⟦ x ⟧asString) (convertElementType e) (convertTensorShape t)
convertInputDefinition (inputOnnxDef x₁ e t x₂) = declareInput (SVariableName ⟦ x₁ ⟧asString) (convertElementType e) (convertTensorShape t)

-- convertHiddenDefinition : 𝐁.HiddenDefinition → 𝐕.HiddenDefinition

convertOutputDefinition : 𝐁.OutputDefinition → 𝐕.OutputDefinition
convertOutputDefinition (outputDef x e t) = declareOutput (SVariableName ⟦ x ⟧asString) (convertElementType e) (convertTensorShape t)
convertOutputDefinition (outputOnnxDef x₁ e t x₂) = declareOutput (SVariableName ⟦ x₁ ⟧asString) (convertElementType e) (convertTensorShape t)

convertNetworkDefinition : 𝐁.NetworkDefinition → 𝐕.NetworkDefinition
convertNetworkDefinition (networkDef x is _ os) = declareNetwork (convertVariableName x) (List.map convertInputDefinition is) (List.map convertOutputDefinition os)

convertNetworkDefs : List⁺ 𝐁.NetworkDefinition → List 𝐕.NetworkDefinition
convertNetworkDefs networkDefs = List.map convertNetworkDefinition (toList networkDefs)

-- Get variable Names
inputVars : 𝐁.InputDefinition → 𝐁.VariableName
inputVars (inputDef x e t) = x
inputVars (inputOnnxDef x₁ e t x₂) = x₁

hiddenVars : 𝐁.HiddenDefinition → 𝐁.VariableName
hiddenVars (hiddenDef x₁ e t x₂) = x₁

outputVars : 𝐁.OutputDefinition → 𝐁.VariableName
outputVars (outputDef x e t) = x
outputVars (outputOnnxDef x₁ e t x₂) = x₁

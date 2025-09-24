module vnnlib-semantics where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Fin as Fin
open import Data.Product as Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty using (⊥)

open import utils
open import vnnlib-types
open import vnnlib-syntax
open import tensor using (Tensor; TensorShape; tensorLookup)

    
-- Network Implementation Representation
SetOfTensors : List (TensorShape × ElementType) → Set 
SetOfTensors tensorsInfo =
  (i : Fin (List.length tensorsInfo)) → let shape&type = List.lookup tensorsInfo i in Tensor (ElementTypeToSet (proj₂ shape&type)) (proj₁ shape&type) 

NetworkImplementation : NetworkType → Set
NetworkImplementation networkτ = SetOfTensors inputs → SetOfTensors outputs
  where
    inputs = NetworkType.inputShapes&Types networkτ
    outputs = NetworkType.outputShapes&Types networkτ

-- Environment Representation
Assignments : Context → Set
Assignments Γ = 
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in SetOfTensors (NetworkType.inputShapes&Types networkType)

NetworkImplementations : Context → Set
NetworkImplementations Γ = 
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in NetworkImplementation networkType

Environment : Context → Set
Environment Γ = NetworkImplementations Γ × Assignments Γ

-- Semantics of Assertions
module _ (Γ : Context) (ε : Environment Γ) where

  module _ (τ : ElementType) where
    ⟦_⟧ₐ : ArithExpr Γ τ → ElementTypeToSet τ
    ⟦ (constant a) ⟧ₐ         = a
    ⟦ (negate a) ⟧ₐ           = 0ℚ ℚ.- ⟦ a ⟧ₐ 
    ⟦ (varInput iₙₑₜ jᵢₙₚ indices ) ⟧ₐ    = tensorLookup indices (((proj₂ ε) iₙₑₜ) jᵢₙₚ)
    ⟦ (varOutput iₙₑₜ jₒᵤₜ indices ) ⟧ₐ   = tensorLookup indices (((((proj₁ ε) iₙₑₜ) (((proj₂ ε) iₙₑₜ))) jₒᵤₜ))
    ⟦ (add []) ⟧ₐ             = 0ℚ
    ⟦ (add (a₀ ∷ a)) ⟧ₐ       = ⟦ a₀ ⟧ₐ ℚ.+ ⟦ (add a) ⟧ₐ
    ⟦ (mult []) ⟧ₐ            = 1ℚ
    ⟦ (mult (a₀ ∷ a)) ⟧ₐ      = ⟦ a₀ ⟧ₐ ℚ.* ⟦ (mult a) ⟧ₐ
    ⟦ (minus []) ⟧ₐ           = 0ℚ
    ⟦ (minus (a₀ ∷ a)) ⟧ₐ     = ⟦ a₀ ⟧ₐ ℚ.- ⟦ (add a) ⟧ₐ

    ⟦_⟧ᶜ : CompExpr Γ τ → Bool
    ⟦ greaterThan x x₁ ⟧ᶜ = ⟦ x ⟧ₐ >ᵇ ⟦ x₁ ⟧ₐ
    ⟦ lessThan x x₁ ⟧ᶜ = ⟦ x ⟧ₐ <ᵇ ⟦ x₁ ⟧ₐ
    ⟦ greaterEqual x x₁ ⟧ᶜ = ⟦ x ⟧ₐ ≥ᵇ ⟦ x₁ ⟧ₐ
    ⟦ lessEqual x x₁ ⟧ᶜ = ⟦ x ⟧ₐ ℚ.≤ᵇ ⟦ x₁ ⟧ₐ
    ⟦ notEqual x x₁ ⟧ᶜ = ⟦ x ⟧ₐ ≠ᵇ ⟦ x₁ ⟧ₐ
    ⟦ equal x x₁ ⟧ᶜ = ⟦ x ⟧ₐ =ᵇ ⟦ x₁ ⟧ₐ

  ⟦_⟧ᵇ : BoolExpr Γ → Bool
  ⟦ (literal b) ⟧ᵇ          = b
  ⟦ compExpr (fst , snd) ⟧ᵇ = ⟦ fst ⟧ᶜ snd
  ⟦ (andExpr []) ⟧ᵇ         = true
  ⟦ (andExpr (b ∷ xb)) ⟧ᵇ   = _∧_ ⟦ b ⟧ᵇ ⟦ (andExpr xb) ⟧ᵇ
  ⟦ (orExpr []) ⟧ᵇ          = false
  ⟦ (orExpr (b ∷ xb)) ⟧ᵇ    = _∨_ ⟦ b ⟧ᵇ ⟦  (orExpr xb) ⟧ᵇ

  ⟦_⟧ₚ : Assertion Γ → Bool
  ⟦ (assert p) ⟧ₚ = ⟦ p ⟧ᵇ

-- Semantics of a Query
⟦_⟧𝕢 : Query → Set
⟦ mkQuery networks assertions ⟧𝕢 =
  let Γ = mkContext networks in (n : NetworkImplementations Γ) → ∃ λ (x : Assignments Γ) → List.foldl (λ z z₁ → and (z ∷ ⟦ Γ ⟧ₚ (n , x) z₁ ∷ [])) true assertions ≡ true




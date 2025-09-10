module vnnlib-semantics where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Nat as ℕ hiding (_<ᵇ_)
open import Data.Integer
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Product.Nary.NonDependent as Nary
open import Data.Fin as Fin
open import Data.Product as Product
open import Level
open import Function.Nary.NonDependent as NFunc
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst)

open import utils
open import vnnlib-types
open import vnnlib-syntax
open import tensor using (Tensor; TensorShape; tensorLookup)


-- Pending on std-lib update from vehicle-lang/vehicle-formalisation
stabulate : ∀ n → (f : Fin n → Level) → (g : (i : Fin n) → Set (f i)) → Sets n (ltabulate n f)
stabulate ℕ.zero f g = _
stabulate (suc n) f g = g Fin.zero , stabulate n (f ∘′ Fin.suc) (λ u → g (Fin.suc u))

-- special proj for nnary products from stabulate
projₙ-stabulate : ∀ n (f : Fin n → Level) (g : (i : Fin n) → Set (f i)) k → Product n (stabulate n f g) → g k
projₙ-stabulate (ℕ.suc ℕ.zero) f g Fin.zero prod = prod
projₙ-stabulate (2+ n) f g Fin.zero prod = proj₁ prod
projₙ-stabulate (2+ n) f g (Fin.suc k) prod = projₙ-stabulate (ℕ.suc n) (f ∘′ Fin.suc) (λ u → g (Fin.suc u))  k (proj₂ prod)

    
-- Network Implementation Representation
ProductOfTensorsLevel : List TensorShape → Level
ProductOfTensorsLevel shapes = NFunc.⨆ (List.length shapes ) (ltabulate (List.length shapes) (λ i → Level.zero))

ProductOfTensors : (shapes : List TensorShape) → Set (ProductOfTensorsLevel shapes) 
ProductOfTensors shapes = Nary.Product ni (stabulate ni (λ i → Level.zero) (λ i → Tensor ℚ (List.lookup shapes i)) )
  where ni = List.length shapes

record NetworkImplementation (networkType : NetworkType) : Set
       (ProductOfTensorsLevel (NetworkType.inputShape networkType) Level.⊔ ProductOfTensorsLevel (NetworkType.outputShape networkType)) where
  constructor
    network
  open NetworkType networkType
  field
    networkFunction : ProductOfTensors inputShape → ProductOfTensors outputShape
    inputTensors : ProductOfTensors inputShape

Environment : Context → Setω
Environment Γ =
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in NetworkImplementation networkType


module _ (Γ : Context) (ε : Environment Γ) where
  open NetworkImplementation

  module _ (τ : ElementType) where
    ⟦_⟧ₐ : ArithExpr Γ τ → ElementTypeToSet τ
    ⟦ (constant a) ⟧ₐ         = a
    ⟦(negate a) ⟧ₐ            = 0ℚ ℚ.- ⟦ a ⟧ₐ 
    ⟦ (varInput iₙₑₜ jᵢₙₚ indices ) ⟧ₐ    = tensorLookup indices (projₙ-stabulate _ _ _ jᵢₙₚ (inputTensors (ε iₙₑₜ)))
    ⟦ (varOutput iₙₑₜ jₒᵤₜ indices ) ⟧ₐ   = tensorLookup indices (projₙ-stabulate _ _ _ jₒᵤₜ (networkFunction (ε iₙₑₜ) (inputTensors (ε iₙₑₜ))))
    -- Cannot simplify similar cases with fold as context is implicit
    ⟦ (add []) ⟧ₐ             = 0ℚ
    ⟦ (add (a₀ ∷ a)) ⟧ₐ       = ⟦ a₀ ⟧ₐ ℚ.+ ⟦ (add a) ⟧ₐ
    ⟦ (mult []) ⟧ₐ            = 1ℚ
    ⟦ (mult (a₀ ∷ a)) ⟧ₐ      = ⟦ a₀ ⟧ₐ ℚ.* ⟦ (mult a) ⟧ₐ
    ⟦ (minus []) ⟧ₐ           = 0ℚ
    ⟦ (minus (a₀ ∷ a)) ⟧ₐ     = ⟦ a₀ ⟧ₐ ℚ.- ⟦ (minus a) ⟧ₐ

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

  
⟦_⟧q : Query → Set
⟦ mkQuery networks x ⟧q = let ctx = mkContext networks in {!!}



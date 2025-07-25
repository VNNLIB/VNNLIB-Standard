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
open import vnnlib-syntax
open import tensor using (Tensor; TensorShape; tensorLookup)


-- Pending on std-lib update from vehicle-lang/vehicle-formalisation
stabulate : ∀ n → (f : Fin n → Level) → (g : (i : Fin n) → Set (f i)) → Sets n (ltabulate n f)
stabulate ℕ.zero f g = _
stabulate (suc n) f g = g Fin.zero , stabulate n (f ∘′ Fin.suc) (λ u → g (Fin.suc u))

    
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
  domainCardinality : ℕ
  domainCardinality = List.length inputShape
  codomainCardinality : ℕ
  codomainCardinality = List.length outputShape

Environment : Context → Setω
Environment Γ =
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in NetworkImplementation networkType

-- WIP: proofs that NetworkImplementation.domainCardinality and codomainCardinality is the same value as the list length of the number of inputs and outputs
domainCardinality-eq : ∀ {Γ} (ε : Environment Γ) (i : Fin (List.length Γ)) → NetworkImplementation.domainCardinality (ε i) ≡ List.length (NetworkType.inputShape (List.lookup Γ i))
domainCardinality-eq ε i = Eq.refl

jᵢ : ∀ {Γ} (ε : Environment Γ) (i : Fin (List.length Γ)) (j : Fin (List.length (NetworkType.inputShape (List.lookup Γ i)))) →  Fin (NetworkImplementation.domainCardinality (ε i))
jᵢ ε i j = subst Fin (domainCardinality-eq ε i) j

codomainCardinality-eq : ∀ {Γ} (ε : Environment Γ) (i : Fin (List.length Γ)) → NetworkImplementation.codomainCardinality (ε i) ≡ List.length (NetworkType.outputShape (List.lookup Γ i))
codomainCardinality-eq ε i = Eq.refl

jₒ : ∀ {Γ} (ε : Environment Γ) (i : Fin (List.length Γ)) (j : Fin (List.length (NetworkType.outputShape (List.lookup Γ i)))) →  Fin (NetworkImplementation.codomainCardinality (ε i))
jₒ ε i j = subst Fin (codomainCardinality-eq ε i) j


module _ (Γ : Context) (ε : Environment Γ) where
         
  ⟦_⟧ₐ : ArithExpr Γ → ℚ
  ⟦ (constant a) ⟧ₐ         = a
  ⟦(negate a) ⟧ₐ            = 0ℚ ℚ.- ⟦ a ⟧ₐ 
  ⟦ (varInput i j n ) ⟧ₐ    = tensorLookup n (projₙ (NetworkImplementation.domainCardinality (ε i)) {!!} (NetworkImplementation.inputTensors (ε i)))
  ⟦ (varOutput i j n ) ⟧ₐ   = tensorLookup n (projₙ (NetworkImplementation.codomainCardinality (ε i)) {!!} (NetworkImplementation.networkFunction (ε i) (NetworkImplementation.inputTensors (ε i)))) 
  -- Cannot simplify similar cases with fold as context is implicit
  ⟦ (add []) ⟧ₐ             = 0ℚ
  ⟦ (add (a₀ ∷ a)) ⟧ₐ       = ⟦ a₀ ⟧ₐ ℚ.+ ⟦ (add a) ⟧ₐ
  ⟦ (mult []) ⟧ₐ            = 1ℚ
  ⟦ (mult (a₀ ∷ a)) ⟧ₐ      = ⟦ a₀ ⟧ₐ ℚ.* ⟦ (mult a) ⟧ₐ
  ⟦ (minus []) ⟧ₐ           = 0ℚ
  ⟦ (minus (a₀ ∷ a)) ⟧ₐ     = ⟦ a₀ ⟧ₐ ℚ.- ⟦ (minus a) ⟧ₐ


  ⟦_⟧ᵇ : BoolExpr Γ → Bool
  ⟦ (literal b) ⟧ᵇ          = b
  ⟦ (greaterThan a1 a2) ⟧ᵇ  = ⟦ a1 ⟧ₐ >ᵇ ⟦ a2 ⟧ₐ
  ⟦ (lessThan a1 a2) ⟧ᵇ     = ⟦ a1 ⟧ₐ <ᵇ ⟦ a2 ⟧ₐ
  ⟦ (greaterEqual a1 a2) ⟧ᵇ = ⟦ a1 ⟧ₐ ≥ᵇ ⟦ a2 ⟧ₐ
  ⟦ (lessEqual a1 a2) ⟧ᵇ    = ⟦ a1 ⟧ₐ ℚ.≤ᵇ ⟦ a2 ⟧ₐ
  ⟦ (notEqual a1 a2) ⟧ᵇ     = ⟦ a1 ⟧ₐ ≠ᵇ ⟦ a2 ⟧ₐ
  ⟦ (equal a1 a2) ⟧ᵇ        = ⟦  a1 ⟧ₐ =ᵇ ⟦ a2 ⟧ₐ
  ⟦ (andExpr []) ⟧ᵇ         = true
  ⟦ (andExpr (b ∷ xb)) ⟧ᵇ   = _∧_ ⟦ b ⟧ᵇ ⟦ (andExpr xb) ⟧ᵇ
  ⟦ (orExpr []) ⟧ᵇ          = false
  ⟦ (orExpr (b ∷ xb)) ⟧ᵇ    = _∨_ ⟦ b ⟧ᵇ ⟦  (orExpr xb) ⟧ᵇ

  ⟦_⟧ₚ : Property Γ → Bool
  ⟦ (assert p) ⟧ₚ = ⟦ p ⟧ᵇ



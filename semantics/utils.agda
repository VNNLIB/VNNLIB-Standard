module utils where

open import Data.Rational using (ℚ; _≤ᵇ_)
open import Data.Bool using (Bool; not; _∧_)
open import Data.List.Base using (List; map; length; _∷_; []; lookup)
open import Data.List.Properties using (length-map)
open import Data.Fin
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; subst; module ≡-Reasoning; cong)
open Eq.≡-Reasoning
open import Data.Vec as V using (Vec)

infix 4 _≥ᵇ_ _>ᵇ_ _<ᵇ_ _=ᵇ_ _≠ᵇ_ 

_≥ᵇ_ : ℚ → ℚ → Bool
p ≥ᵇ q = q ≤ᵇ p

_>ᵇ_ : ℚ → ℚ → Bool
p >ᵇ q = not (p ≤ᵇ q)

_<ᵇ_ : ℚ → ℚ → Bool
p <ᵇ q = not (q ≤ᵇ p)

_=ᵇ_ : ℚ → ℚ → Bool
p =ᵇ q = (q ≤ᵇ p) ∧ (p ≤ᵇ q)

_≠ᵇ_ : ℚ → ℚ → Bool
p ≠ᵇ q = not ((q ≤ᵇ p) ∧ (p ≤ᵇ q))

lookup-map : {A B : Set} → (f : A → B) → (xs : List A) → (i : Fin (length xs)) → lookup (map f xs) (cast (sym (length-map f xs)) i) ≡ f (lookup xs i)
lookup-map f (x ∷ a) zero = refl
lookup-map f (x ∷ a) (suc b) = lookup-map f a b

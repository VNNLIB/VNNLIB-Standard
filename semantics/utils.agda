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

lookup-head : ∀ {A : Set} {x : A} (xs : List A) → lookup (x ∷ xs) zero ≡ x
lookup-head a = refl

-- subst-zero : ∀ {n m : ℕ} (p : n ≡ m) → subst Fin p zero ≡ zero
-- subst-zero refl = refl

length-map-cons : ∀ {A B : Set} (f : A → B) (x : A) (xs : List A) → length (map f (x ∷ xs)) ≡ ℕ.suc (length (map f xs))
length-map-cons f x xs = refl

postulate lookup-map : {A B : Set} → (f : A → B) → (xs : List A) → (i : Fin (length xs)) → lookup (map f xs) (subst Fin (sym (length-map f xs)) i) ≡ f (lookup xs i)
-- lookup-map f (x ∷ a) zero = {!!}
-- lookup-map f (x ∷ a) (suc b) = lookup-map f {!!} {!!}

-- lookup-map₁ : ∀ {A B} (f : A → B) (xs : List A) (i : Fin (length xs)) →
--  lookup (map f xs) (subst Fin (sym (length-map f xs)) i) ≡ f (lookup xs i)
-- lookup-map₁ f [] ()
-- lookup-map₁ f (x ∷ xs) zero    rewrite length-map f xs = refl
-- lookup-map₁ f (x ∷ xs) (suc i) rewrite length-map f xs = lookup-map₁ f xs i



-- lookup-map₁ : ∀ {n : ℕ} {A B : Set} (i : Fin n) (f : A → B) (xs : Vec A n) → V.lookup (V.map f xs) i ≡ f (V.lookup xs i)
-- lookup-map₁ zero    f (x ∷ xs) = refl
-- lookup-map₁ (suc i) f (x ∷ xs) = lookup-map i f xs

module utils where

open import Data.Rational using (ℚ; _≤ᵇ_)
open import Data.Bool using (Bool; not; _∧_)
open import Data.List.Base using (List; map; length; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Data.List.Properties using (length-map)

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


double-length-map : ∀ {A B C : Set} (a : C → A) (c : B → C) (b : List B) → length (map a (map c b)) ≡ length b
double-length-map a c b = trans (length-map a (map c b)) (length-map c b)

-- length-map-n : ∀ {A₀ A₁ … Aₙ : Set} (fs : List (Σ Set (λ A → A → A))) -- list of functions f₁ : A₁ → A₂, f₂ : A₂ → A₃, ..., fₙ : Aₙ₋₁ → Aₙ
--                (b : List A₀) →
--                length (foldr (λ f xs → map (proj₂ f) xs) b fs) ≡ length b
-- length-map-n [] b = refl
-- length-map-n (f ∷ fs) b = trans (length-map (proj₂ f) (foldr (λ f xs → map (proj₂ f) xs) b fs))
--                                 (length-map-n fs b)

-- length (map f₁ (map f₂ (... (map fₙ xs) ...))) ≡ length xs

module types-utils where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺; fromList)

-- The result type
data Result (A : Set) : Set where
  error : Result A
  success : A → Result A

convertMaybeToResult : {A : Set} → Maybe A → Result A
convertMaybeToResult (just x) = success x
convertMaybeToResult nothing = error

convertListToList⁺ : {A : Set} → List A → Result (List⁺ A)
convertListToList⁺ lst = convertMaybeToResult (fromList lst)
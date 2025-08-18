module types-utils where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺; fromList)
open import Data.String using (String)
open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error)
open import Effect.Monad

open RawMonad monad

-- convertM : {A : Set} → Maybe A → Result A
-- convertM (just x) = return x
-- convertM nothing = error "No value"

-- fun1 : ℕ → String → Result ℕ
-- fun1 zero err = error err
-- fun1 (suc n) _ = return n

-- fun2 : ℕ → Result ℕ
-- fun2 n = do
--   u ← fun1 ℕ.zero "not zero" 
--   return (u + n)

convertMaybeToResult : {A : Set} → Maybe A → Result A
convertMaybeToResult (just x) = return x
convertMaybeToResult nothing = error "Empty List"

convertListToList⁺ : {A : Set} → List A → Result (List⁺ A)
convertListToList⁺ lst = do
  let convertedList = fromList lst
  res ← convertMaybeToResult (convertedList)
  return res


useRes : {A : Set} → Result A → Result A
useRes r = do
  x ← r
  return x -- Example operation, can be modified as needed
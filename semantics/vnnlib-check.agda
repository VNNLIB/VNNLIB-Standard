module vnnlib-check where

open import Data.Product as Product using (proj₂)
open import Data.String as String using (String)
open import Data.List as List hiding (foldl)
open import Data.List.NonEmpty as List⁺
open import Syntax.AST as 𝐁 hiding (String)

open import vnnlib-syntax as 𝐕
open import syntax-utils
open import types-utils
open import vnnlib-check-declarations
open import vnnlib-check-assertions
open import context-isomorphism

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

scopeCheckAssertions : (Σ : CheckContext) → List⁺ 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
scopeCheckAssertions Σ asserts = List⁺.foldl checkAssertₙ checkAssert asserts
  where
    checkAssert : 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
    checkAssert (assert b) with checkBoolExpr Σ b
    ... | error _ = error ""
    ... | success x = success (List.[ assert x ])
    checkAssertₙ : Result (List (𝐕.Assertion (convertΣtoΓ Σ))) → 𝐁.Assertion → Result (List (𝐕.Assertion (convertΣtoΓ Σ)))
    checkAssertₙ (error _) _ = error ""
    checkAssertₙ (success props) a with checkAssert a
    ... | error _ = error ""
    ... | success x = success (x ++ props)

-- Check Assertions from the constructed Scope Context
checkAssertions : List 𝐁.NetworkDefinition → List⁺ 𝐁.Assertion → Result 𝐕.Query
checkAssertions defs asserts with mkCheckContext defs
... | error _ = error ""
... | success Σ with scopeCheckAssertions Σ asserts
... | error _ = error ""
... | success x = success (𝐕.mkQuery checkedNetworkDefs x) -- mkCheckContext should return the networkdefs
  where
    checkedNetworkDefs : List 𝐕.NetworkDefinition
    checkedNetworkDefs = List.map proj₂ Σ

-- change to non-empty list
scopeCheck : 𝐁.Query → Result 𝐕.Query
scopeCheck (vNNLibQuery ver ns as) = asserts⁺ (convertListToList⁺ as)
  where
    asserts⁺ : Result (List⁺ 𝐁.Assertion) → Result 𝐕.Query
    asserts⁺ (error _) = error "Cannot have no assertions"
    asserts⁺ (success x₁) = checkAssertions ns x₁

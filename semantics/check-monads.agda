module check-monads where

open import Data.String
open import Data.Sum
open import Data.Nat
open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to TC)
-- rename to throwError, return
open import Effect.Monad

open RawMonad monad

fun1 : ℕ → TC ℕ
fun1 zero = inj₁ "zero"
fun1 (suc n) = inj₂ n

fun2 : ℕ → TC ℕ
fun2 n = do
  u ← fun1 {!!}
  {!!}

module vnnlib-types where

open import Data.Rational as ℚ hiding (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)

-- -- Element Types
data ElementType : Set where
  real         : ElementType
  float16      : ElementType
  float32      : ElementType
  float64      : ElementType
  bfloat16     : ElementType
  float8e4m3fn : ElementType
  float8e5m2   : ElementType
  float8e4m3fnuz : ElementType
  float8e5m2fnuz : ElementType
  float4e2m1   : ElementType
  int8         : ElementType
  int16        : ElementType
  int32        : ElementType
  int64        : ElementType
  uint8        : ElementType
  uint16       : ElementType
  uint32       : ElementType
  uint64       : ElementType
  complex64    : ElementType
  complex128   : ElementType
  boolType     : ElementType
  stringType   : ElementType

-- Add semantics for each type
ElementTypeToSet : ElementType → Set
ElementTypeToSet e = ℚ


postulate _≟_ : (x y : ElementType) → Dec (x ≡ y)
-- a ≟ b = {!   !}

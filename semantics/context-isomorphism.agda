{-# OPTIONS --allow-unsolved-metas #-}
module context-isomorphism where

open import Data.Nat as ℕ
open import Data.List as List
open import Data.List.NonEmpty as List⁺ using (toList; List⁺)
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; module ≡-Reasoning; cong)
open Eq.≡-Reasoning
open import Data.List.Properties using (length-map)
open import Data.Product as Product using (proj₂; proj₁)
open import vnnlib-syntax as 𝐕
open import check

open import utils

convertΣtoΓ : CheckContext → Context
convertΣtoΓ Σ = mkContext (List.map proj₂ (toList Σ))


-- Proof that the length of the CheckContext and the Syntax context are equivalent
length-CheckContext-Context :
  (Σ : CheckContext) →
  List.length (toList Σ) ≡ List.length (convertΣtoΓ Σ)
length-CheckContext-Context Σ = begin
  List.length (toList Σ)                              ≡⟨ sym (length-map proj₂ (toList Σ)) ⟩
  List.length (List.map proj₂ (toList Σ))             ≡⟨ sym (length-map convertNetworkΓ (List.map proj₂ (toList Σ))) ⟩
  List.length (mkContext (List.map proj₂ (toList Σ))) ≡⟨⟩
  List.length (convertΣtoΓ Σ)                         ∎

-- Proof that the length of inputs in a CheckContext NetworkBinding and Syntax Context Network type are equivalent
length-inputs :
  {Σ : CheckContext}
  {n : Fin (List.length (toList Σ))} →
  List.length 
    (toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) n))))
  ≡
  List.length
    (NetworkType.inputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n)))
length-inputs {Σ} {n} = {!!}
  where
    nb = toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) n)))
    nt = NetworkType.inputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n))

length-outputs :
  {Σ : CheckContext}
  {n : Fin (List.length (toList Σ))} →
  List.length
    (toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) n))))
  ≡
  List.length
    (NetworkType.outputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n)))
length-outputs {Σ} {n} = {!!}
  where
    nb = toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) n)))
    nt = NetworkType.outputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n))

-- tensorShape-input : (Σ : CheckContext) → (i : Fin (List.length (toList Σ))) → (j : Fin (List.length (toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) i))))))
--   → getTensorShape (List.lookup (toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) i)))) j)
--     ≡ List.lookup (𝐕.NetworkType.inputShape (𝐕.convertNetworkΓ (proj₂ (List.lookup (toList Σ) i)))) j
-- tensorShape-input Σ i j = refl

-- tensorShape-output : (Σ : CheckContext) (i : Fin (List.length (toList Σ))) (j : Fin (List.length (toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) i)))))) →
--   getTensorShape (List.lookup (toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) i)))) j)
--   ≡ List.lookup (𝐕.NetworkType.outputShape (𝐕.convertNetworkΓ (proj₂ (List.lookup (toList Σ) i)))) j
-- tensorShape-output Σ i j = refl

{-# OPTIONS --allow-unsolved-metas #-}
module context-isomorphism where

open import Data.Nat as ℕ
open import Data.List as List
open import Data.List.NonEmpty as List⁺ using (toList; List⁺)
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; trans; module ≡-Reasoning; cong)
open Eq.≡-Reasoning
open import Data.List.Properties using (length-map)
open import Data.Product as Product using (proj₂; proj₁)
open import vnnlib-syntax as 𝐕
open import vnnlib-check-declarations

open import utils

convertΣtoΓ : CheckContext → Context
convertΣtoΓ Σ = mkContext (List.map proj₂ Σ)


-- Proof that the length of the CheckContext and the Syntax context are equivalent
length-CheckContext-Context :
  (Σ : CheckContext) →
  List.length Σ ≡ List.length (convertΣtoΓ Σ)
length-CheckContext-Context Σ = begin
  List.length Σ                              ≡⟨ sym (length-map proj₂ Σ) ⟩
  List.length (List.map proj₂ Σ)             ≡⟨ sym (length-map convertNetworkΓ (List.map proj₂ Σ)) ⟩
  List.length (mkContext (List.map proj₂ Σ)) ≡⟨⟩
  List.length (convertΣtoΓ Σ)                         ∎

-- Proof that the length of inputs in a CheckContext NetworkBinding and Syntax Context Network type are equivalent
cong-input :
  (Σ : CheckContext)
  (n : Fin (List.length Σ)) →
  List.length (toList (NetworkBinding.inputs (proj₁ (lookup Σ n)))) ≡ List.length (NetworkType.inputShape (convertNetworkΓ (proj₂ (lookup Σ n))))
cong-input Σ n = begin 
  List.length (toList (NetworkBinding.inputs (proj₁ (lookup Σ n)))) ≡⟨ {!!} ⟩
  List.length (NetworkType.inputShape (convertNetworkΓ (proj₂ (lookup Σ n)))) ∎
  

length-inputs :
  (Σ : CheckContext)
  (n : Fin (List.length Σ)) →
  List.length 
    (toList (NetworkBinding.inputs (proj₁ (List.lookup Σ n))))
  ≡
  List.length
    (NetworkType.inputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n)))
length-inputs Σ n = begin
  List.length (toList (NetworkBinding.inputs (proj₁ (List.lookup Σ n))))            ≡⟨ cong-input Σ n ⟩
  List.length (NetworkType.inputShape (convertNetworkΓ (proj₂ (List.lookup Σ n))))  ≡⟨ {!!} ⟩ --  sym (length-map convertInputΓ {!!}) ⟩ -- sym (length-map {!!} {!!}) ⟩
  List.length (NetworkType.inputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n))) ∎

cong-output :
  (Σ : CheckContext)
  (n : Fin (List.length Σ)) →
  List.length (toList (NetworkBinding.outputs (proj₁ (lookup Σ n)))) ≡ List.length (NetworkType.outputShape (convertNetworkΓ (proj₂ (lookup Σ n))))
cong-output Σ n = begin 
  List.length (toList (NetworkBinding.outputs (proj₁ (lookup Σ n)))) ≡⟨ {!!} ⟩
  List.length (NetworkType.outputShape (convertNetworkΓ (proj₂ (lookup Σ n)))) ∎

length-outputs :
  (Σ : CheckContext)
  (n : Fin (List.length Σ)) →
  List.length
    (toList (NetworkBinding.outputs (proj₁ (List.lookup Σ n))))
  ≡
  List.length
    (NetworkType.outputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n)))
length-outputs Σ n = begin
  List.length (toList (NetworkBinding.outputs (proj₁ (List.lookup Σ n))))            ≡⟨ {!!} ⟩ 
  List.length (NetworkType.outputShape (convertNetworkΓ (proj₂ (List.lookup Σ n))))  ≡⟨ {!!} ⟩
  List.length (NetworkType.outputShape (List.lookup (convertΣtoΓ Σ) (subst Fin (length-CheckContext-Context Σ) n))) ∎

-- tensorShape-input : (Σ : CheckContext) → (i : Fin (List.length (toList Σ))) → (j : Fin (List.length (toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) i))))))
--   → getTensorShape (List.lookup (toList (NetworkBinding.inputs (proj₁ (List.lookup (toList Σ) i)))) j)
--     ≡ List.lookup (𝐕.NetworkType.inputShape (𝐕.convertNetworkΓ (proj₂ (List.lookup (toList Σ) i)))) j
-- tensorShape-input Σ i j = refl

-- tensorShape-output : (Σ : CheckContext) (i : Fin (List.length (toList Σ))) (j : Fin (List.length (toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) i)))))) →
--   getTensorShape (List.lookup (toList (NetworkBinding.outputs (proj₁ (List.lookup (toList Σ) i)))) j)
--   ≡ List.lookup (𝐕.NetworkType.outputShape (𝐕.convertNetworkΓ (proj₂ (List.lookup (toList Σ) i)))) j
-- tensorShape-output Σ i j = refl

open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary
open import Data.Sum
open import Data.Product
open import Data.List.Membership.Propositional 
open import Level
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open import Relation.Binary.Construct.Union
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

open import Stoughton.Var

module BetaConversion (𝒞 : Set) {𝒱 : Set} (var : IsVar 𝒱) where

  open import Stoughton.Syntax 𝒞 𝒱 (IsVar._≟_ var)  
  open import Stoughton.Alpha 𝒞 var
  open import Stoughton.Substitution 𝒞 var      
  open import Stoughton.SubstitutionLemmas 𝒞 var
  open import CxtClosure 𝒞 var  
  open import BetaReduction 𝒞 var

  infix 3 _≃β_

  _≃β_ = EqClosure (_∼α_ ∪ _→β_) -- Plus⇔ _→αβ_  --Plus⇔ _⇉α_

  lemma∼α⊆≃β : _∼α_ ⇒ _≃β_
  lemma∼α⊆≃β M∼N = inj₁ (inj₁ M∼N) ◅ ε
    
  compatConvSub : ∀ {M N σ} → M ≃β N → M ∙ σ ≃β N ∙ σ
  compatConvSub ε = ε
  compatConvSub (inj₁ (inj₁ M∼j) ◅ j≃N) = inj₁ (inj₁ (≡⇒∼ (compatSubAlpha M∼j))) ◅ compatConvSub j≃N  
  compatConvSub (inj₁ (inj₂ M→j) ◅ j≃N) with compatRedSub M→j
  ... | P , Mσ→P , P∼jσ = inj₁ (inj₂ Mσ→P) ◅ inj₁ (inj₁ P∼jσ) ◅ compatConvSub j≃N
  compatConvSub (inj₂ (inj₁ j∼M) ◅ j≃N) = inj₂ (inj₁ (≡⇒∼ (compatSubAlpha j∼M))) ◅ compatConvSub j≃N  
  compatConvSub (inj₂ (inj₂ j→M) ◅ j≃N) with compatRedSub j→M
  ... | P , jσ→P , P∼Mσ = inj₂ (inj₁ P∼Mσ) ◅ inj₂ (inj₂ jσ→P) ◅ compatConvSub j≃N

{-
  infix 3 _≃βˢ_
  _≃βˢ_ : Sub → Sub → Set
  σ ≃βˢ σ' = ∀ x → σ x ≃β σ' x
  
  compatConvConvSub : ∀ {M M' σ σ'} → M ≃β M' → σ ≃βˢ σ' →  M ∙ σ ≃β M' ∙ σ'
  compatConvConvSub = {!!}
-}

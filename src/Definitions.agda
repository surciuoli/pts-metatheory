open import Stoughton.Var

module Definitions (𝒞 : Set) {𝒱} (enum : Enum 𝒱) where

  open Enum enum
  
  open import Data.Product
  open import Data.Empty
  open import Relation.Nullary
  open import Data.List.Membership.DecPropositional _≟_
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 enum
  open import Stoughton.SubstitutionLemmas 𝒞 enum
  open import Stoughton.Alpha 𝒞 enum

  AntiPreserves* : (Λ → Λ → Set) → Set
  AntiPreserves* r = ∀ {x M N} → x * N → r M N → x * M

  Preserves# : (Λ → Λ → Set) → Set
  Preserves# r = ∀ {x M N} → x # M → r M N → x # N

  antipres*⇒pres# : {_▹_ : Λ → Λ → Set} → AntiPreserves* _▹_ → Preserves# _▹_
  antipres*⇒pres# x*N→M▹N→x*M x#M M▹N x*N = ⊥-elim (x#M (x*N→M▹N→x*M x*N M▹N))

  pres#⇒antipres* : {_▹_ : Λ → Λ → Set} → Preserves# _▹_ → AntiPreserves* _▹_
  pres#⇒antipres* x#M→M▹N→x#N {x} {M} {N} x*N M▹N with x ∈? fv M
  ... | yes x*M = x*M
  ... | no x#M = ⊥-elim (x#M→M▹N→x#N x#M M▹N x*N)
  
  Compat∙ : (Λ → Λ → Set) → Set
  Compat∙ r = ∀ {M N σ} → r M N → Σ[ P ∈ Λ ](r (M ∙ σ) P × P ∼α N ∙ σ)

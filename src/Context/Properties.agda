open import Data.List.Relation.Binary.Pointwise as Pw hiding (map; refl)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality 

open import Stoughton.Var

module Context.Properties (𝒞 : Set) {𝒱 : Set} (enum : Enum 𝒱) where

  open Enum enum
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Alpha 𝒞 enum
  open import Stoughton.SubstitutionLemmas 𝒞 enum
  
  open import Context 𝒱 Λ _≟_

  infix 1 _≈α_
  _≈α_ : Cxt → Cxt → Set
  _≈α_ = Pointwise (λ (x , A) (y , B) → x ≡ y × A ∼α B)

  ∼ρs : ∀ {Γ} → Γ ≈α Γ
  ∼ρs = Pw.refl (refl , ∼ρ)

  ∼σs : ∀ {Γ Δ} → Γ ≈α Δ → Δ ≈α Γ
  ∼σs [] = []
  ∼σs ((x=y , A∼B) ∷ xs) = (sym x=y , ∼σ A∼B) ∷ ∼σs xs

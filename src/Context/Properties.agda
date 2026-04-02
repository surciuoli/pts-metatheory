open import Data.List.Relation.Binary.Pointwise as Pw hiding (map; refl)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality 

open import Stoughton.Var

module Context.Properties (𝒞 : Set) {𝒱 : Set} (var : Enum 𝒱) where

  open import Stoughton.Syntax 𝒞 𝒱 (Enum._≟_ var)
  open import Stoughton.Alpha 𝒞 var
  open import Stoughton.SubstitutionLemmas 𝒞 var
  
  open import Context 𝒱 Λ (Enum._≟_ var)

  infix 1 _≈α_
  _≈α_ : Cxt → Cxt → Set
  _≈α_ = Pointwise (λ (x , A) (y , B) → x ≡ y × A ∼α B)

  ∼ρs : ∀ {Γ} → Γ ≈α Γ
  ∼ρs = Pw.refl (refl , ∼ρ)

  ∼σs : ∀ {Γ Δ} → Γ ≈α Δ → Δ ≈α Γ
  ∼σs [] = []
  ∼σs ((x=y , A∼B) ∷ xs) = (sym x=y , ∼σ A∼B) ∷ ∼σs xs

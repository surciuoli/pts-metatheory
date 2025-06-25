open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum 
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Stoughton.Var

module PTS.SyntacticValidity {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where
  
  open import PTS isVar 𝒜 ℛ
  open import PTS.Thinning isVar 𝒜 ℛ
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Context 𝒱 Λ _≟_

  validDecl : ∀ {Γ x A} → Γ ok → (x , A) ∈ Γ → ∃ λ s → Γ ⊢ A ∶ c s
  validDecl ⊢nil ()
  validDecl {.((x , A) ∷ Γ)} {x} {A} Γ,x:Aok@(⊢cons {Γ} {s = s} Γok x∉domΓ Γ⊢A:s) (here refl) =
    s , thinning Γ⊆Γ,x:A Γ,x:Aok Γ⊢A:s
    where
    Γ⊆Γ,x:A : Γ ⊆ (Γ ‚ x ∶ A)
    Γ⊆Γ,x:A = xs⊆x∷xs Γ (x , A)
  validDecl {.((y , B) ∷ Γ)} {x} {A} Γ,x:Bok@(⊢cons {Γ} {y} {_} {B} Γok _ _) (there x,A∈Γ) with validDecl Γok x,A∈Γ
  ... | s , Γ⊢A:s = s , thinning Γ⊆Γ,y:B Γ,x:Bok Γ⊢A:s 
    where
    Γ⊆Γ,y:B : Γ ⊆ (Γ ‚ y ∶ B)
    Γ⊆Γ,y:B = xs⊆x∷xs Γ (y , B)  

  syntacticValidity : ∀ {Γ M A} → Γ ⊢ M ∶ A → ∃ λ s → A ≡ c s ⊎ Γ ⊢ A ∶ c s
  syntacticValidity {Γ} (⊢var Γok x,A∈Γ) with validDecl Γok x,A∈Γ
  ... | s , Γ⊢A:s = s , inj₂ Γ⊢A:s
  syntacticValidity {Γ} Γ⊢s₁:s₂@(⊢sort {s₂ = s₂} _ _) = s₂ , inj₁ refl
  syntacticValidity {Γ} (⊢abs {x} {y} {s₁} {s₂} {s₃} Rs₁s₂s₃ Γ⊢A:s₁ ∀z∉Γ→Γ,z:A⊢B[y=z]:s₂ ∀z∉Γ→Γ,z:A⊢M[x=z]:B[y=z]) =
    s₃ , inj₂ (⊢prod Rs₁s₂s₃ Γ⊢A:s₁ ∀z∉Γ→Γ,z:A⊢B[y=z]:s₂)
  syntacticValidity {Γ} (⊢app {s = s} _ _ Γ⊢[N/x]B:s) = s , inj₂ Γ⊢[N/x]B:s
  syntacticValidity (⊢conv {s = s} _ _ Γ⊢A:s) = s , inj₂ Γ⊢A:s
  syntacticValidity (⊢prod {s₃ = s₃} _ _ _) = s₃ , inj₁ refl

 

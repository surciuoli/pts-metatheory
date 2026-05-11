open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Subset.Propositional
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Binary.Construct.Union
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
open import Data.Empty

open import Stoughton.Var

module PTSs {𝒞 𝒱 : Set} (isVar : Enum 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  private
    _≟_ = Enum._≟_ isVar
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_  
  open import Stoughton.Chi (Enum.encode isVar) (Enum.decode isVar) (Enum.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar
  open import Utils
  
  infix 3 _okₛ 
  infix 3 _⊢ₛ_∶_ 

  mutual
    data _okₛ : Cxt → Set where 
      ⊢nil : [] okₛ 
      ⊢cons : ∀ {Γ x s A}
            → Γ okₛ
            → x ∉ dom Γ
            → Γ ⊢ₛ A ∶ c s
            → Γ ‚ x ∶ A okₛ 

    data _⊢ₛ_∶_ (Γ : Cxt) : Λ → Λ → Set where 
      ⊢var : ∀ {x A}
           → Γ okₛ
           → (x , A) ∈ Γ
           → Γ ⊢ₛ v x ∶ A
      ⊢sort : ∀ {s₁ s₂}
            → Γ okₛ
            → 𝒜 s₁ s₂
            → Γ ⊢ₛ c s₁ ∶ c s₂
      ⊢prod : ∀ {x y s₁ s₂ s₃ A B}
            → ℛ s₁ s₂ s₃
            → Γ ⊢ₛ A ∶ c s₁          
            → y ∉ fv B - x
            → Γ ‚ y ∶ A ⊢ₛ B [ x := v y ] ∶ c s₂
            → Γ ⊢ₛ Π[ x ∶ A ] B ∶ c s₃          
      ⊢abs : ∀ {x y z s₁ s₂ s₃ A B M}
           → ℛ s₁ s₂ s₃      
           → z ∉ fv M - x
           → z ∉ fv B - y
           → Γ ⊢ₛ A ∶ c s₁
           → Γ ‚ z ∶ A ⊢ₛ M [ x := v z ] ∶ B [ y := v z ]
           → Γ ‚ z ∶ A ⊢ₛ B [ y := v z ] ∶ c s₂
           → Γ ⊢ₛ λ[ x ∶ A ] M ∶ Π[ y ∶ A ] B 
      ⊢app : ∀ {x M N A B}
           → Γ ⊢ₛ M ∶ Π[ x ∶ A ] B
           → Γ ⊢ₛ N ∶ A
           → Γ ⊢ₛ M · N ∶ B [ x := N ]
      ⊢conv : ∀ {s M A B}
            → Γ ⊢ₛ M ∶ A
            → A ≃β B
            → Γ ⊢ₛ B ∶ c s
            → Γ ⊢ₛ M ∶ B

  validCxt : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → Γ okₛ
  validCxt (⊢sort Γok _) = Γok
  validCxt (⊢prod _ Γ⊢A:s _ _) = validCxt Γ⊢A:s
  validCxt (⊢var Γok _) = Γok    
  validCxt (⊢abs _ _ _ t _ _) = validCxt t
  validCxt (⊢app t _) = validCxt t
  validCxt (⊢conv t _ _) = validCxt t

  -- inversion (generation) lemmas

  genVar : ∀ {Γ x A} → Γ ⊢ₛ v x ∶ A → ∃ λ B → Γ okₛ × (x , B) ∈ Γ × A ≃β B
  genVar {Γ} {x} {A} (⊢var {.x} {.A} Γok x,A∈Γ) = A , Γok , x,A∈Γ , Eq.reflexive (_∼α_ ∪ _→β_)
  genVar {Γ} {x} {A} (⊢conv {_} {.(v x)} {C} {.A} Γ⊢x:C C≃A _) with genVar Γ⊢x:C
  ... | B , Γok , x,B∈Γ , C≃B = B , Γok , x,B∈Γ , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃A) C≃B

  genSort : ∀ {Γ s A} → Γ ⊢ₛ c s ∶ A → ∃ λ t → Γ okₛ × 𝒜 s t × A ≃β c t
  genSort {Γ} {s} {.(c t)} (⊢sort {.s} {t} Γok 𝒜st) = t , Γok , 𝒜st , Eq.reflexive (_∼α_ ∪ _→β_)
  genSort {Γ} {s} {A} (⊢conv {_} {.(c s)} {C} {.A} Γ⊢s:C C≃A _) with genSort Γ⊢s:C
  ... | t , Γok , 𝒜st , C≃t = t , Γok , 𝒜st , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃A) C≃t

  genLam : ∀ {Γ x A M C} → Γ ⊢ₛ λ[ x ∶ A ] M ∶ C
         → ∃₆ λ s₁ s₂ s₃ x' y B
         → ℛ s₁ s₂ s₃         
         × y ∉ fv M - x
         × y ∉ fv B - x'
         × Γ ⊢ₛ A ∶ c s₁
         × Γ ‚ y ∶ A ⊢ₛ M [ x := v y ] ∶ B [ x' := v y ]
         × Γ ‚ y ∶ A ⊢ₛ B [ x' := v y ] ∶ c s₂
         × C ≃β Π[ x' ∶ A ] B
  genLam (⊢abs {x} {x'} {y} {s₁} {s₂} {s₃} {A} {B} ℛs₁s₂s₃ y∉fvM-x y∉fvB-x' Γ⊢A:s₁ Γ,y:A⊢M[x=y]:B[x'=y] Γ,y:A⊢B[x'=y]:s₂) =
    s₁ , s₂ , s₃ , x' , y , B , ℛs₁s₂s₃ , y∉fvM-x , y∉fvB-x' , Γ⊢A:s₁ , Γ,y:A⊢M[x=y]:B[x'=y] , Γ,y:A⊢B[x'=y]:s₂
    , Eq.reflexive (_∼α_ ∪ _→β_)
  genLam (⊢conv Γ⊢λ[x:A]M:C C≃D _) with genLam Γ⊢λ[x:A]M:C
  ... |  s₁ , s₂ ,  s₃ , x' , y , B , ℛs₁s₂s₃ , y∉fvM-x , y∉fvB-x' , Γ⊢A:s₁ , Γ,y:A⊢M[x=y]:B[x'=y] , Γ,y:A⊢B[x'=y]:s₂ , D≃Π[x':A]B =
    s₁ , s₂ , s₃ , x' , y , B , ℛs₁s₂s₃ , y∉fvM-x , y∉fvB-x' , Γ⊢A:s₁ , Γ,y:A⊢M[x=y]:B[x'=y] , Γ,y:A⊢B[x'=y]:s₂
    , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃D) D≃Π[x':A]B 

  genAbs = genLam

  genApp : ∀ {Γ M N C} → Γ ⊢ₛ M · N ∶ C
         → ∃₃ λ x A B
         → Γ ⊢ₛ M ∶ Π[ x ∶ A ] B
         × Γ ⊢ₛ N ∶ A
         × C ≃β B [ x := N ]
  genApp (⊢app {x} {M} {N} {A} {B} Γ⊢M:Π[x:A]B Γ⊢N:A) = x , A , B , Γ⊢M:Π[x:A]B , Γ⊢N:A , Eq.reflexive (_∼α_ ∪ _→β_)
  genApp (⊢conv Γ⊢MN:D D≃C _) with genApp Γ⊢MN:D
  ... | x , A , B , Γ⊢M:Π[x:A]B , Γ⊢N:A , D≃B[x=N] =
    x , A , B , Γ⊢M:Π[x:A]B , Γ⊢N:A , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) D≃C) D≃B[x=N]
    
  genProd : ∀ {Γ x A B C} → Γ ⊢ₛ Π[ x ∶ A ] B ∶ C
        → ∃₄ λ s₁ s₂ s₃ y
        → ℛ s₁ s₂ s₃
        × Γ ⊢ₛ A ∶ c s₁
        × y ∉ fv B - x
        × Γ ‚ y ∶ A ⊢ₛ B [ x := v y ] ∶ c s₂
        × C ≃β c s₃
  genProd (⊢prod {x} {y} {s₁} {s₂} {s₃} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , Eq.reflexive (_∼α_ ∪ _→β_)        
  genProd (⊢conv Γ⊢Π[x:A]B:C C=D _) with genProd Γ⊢Π[x:A]B:C
  ... | s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , C=s₃ =
    s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C=D) C=s₃

  cxtInj : ∀ {x A B Γ} → (x , A) ∈ Γ → (x , B) ∈ Γ → Γ okₛ → A ≡ B
  cxtInj {.x} {.A} {.A} (here refl) (here refl) (⊢cons {x = x} {A = A} _ _ _) = refl
  cxtInj {.x} {.A} {B} (here refl) (there x,B∈Γ) (⊢cons {x = x} {A = A} _ x∉domΓ _) =
    ⊥-elim (x∉domΓ (inCxtInDom x,B∈Γ))
  cxtInj {.x} {A} {.B} (there x,A∈Γ) (here refl) (⊢cons {x = x} {A = B} _ x∉domΓ _) =
    ⊥-elim (x∉domΓ (inCxtInDom x,A∈Γ))  
  cxtInj (there x,A∈Γ) (there x,B∈Γ) (⊢cons Γok _ _) = cxtInj x,A∈Γ x,B∈Γ Γok   
  

open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Subset.Propositional
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Binary.Construct.Union
open import Relation.Nullary

open import Stoughton.Var

module PTSs2 {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  private
    _≟_ = IsVar._≟_ isVar
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar
  open import Utils
  
  infix 3 _okₛ₂ 
  infix 3 _⊢ₛ₂_∶_ 

  mutual
    data _okₛ₂ : Cxt → Set where 
      ⊢nil : [] okₛ₂ 
      ⊢cons : ∀ {Γ x s A}
            → Γ okₛ₂
            → x ∉ dom Γ
            → Γ ⊢ₛ₂ A ∶ c s
            → Γ ‚ x ∶ A okₛ₂ 

    data _⊢ₛ₂_∶_ (Γ : Cxt) : Λ → Λ → Set where 
      ⊢var : ∀ {x A}
           → Γ okₛ₂
           → (x , A) ∈ Γ
           → Γ ⊢ₛ₂ v x ∶ A
      ⊢sort : ∀ {s₁ s₂}
            → Γ okₛ₂
            → 𝒜 s₁ s₂
            → Γ ⊢ₛ₂ c s₁ ∶ c s₂
      ⊢prod : ∀ {x y s₁ s₂ s₃ A B}
            → ℛ s₁ s₂ s₃
            → Γ ⊢ₛ₂ A ∶ c s₁          
            → y ∉ fv B - x
            → Γ ‚ y ∶ A ⊢ₛ₂ B [ x := v y ] ∶ c s₂
            → Γ ⊢ₛ₂ Π[ x ∶ A ] B ∶ c s₃          
      ⊢abs : ∀ {x y z s A B M}
           → z ∉ fv M - x
           → z ∉ fv B - y
           → Γ ‚ z ∶ A ⊢ₛ₂ M [ x := v z ] ∶ B [ y := v z ]
           → Γ ⊢ₛ₂ Π[ y ∶ A ] B ∶ c s
           → Γ ⊢ₛ₂ λ[ x ∶ A ] M ∶ Π[ y ∶ A ] B 
      ⊢app : ∀ {x M N A B}
           → Γ ⊢ₛ₂ M ∶ Π[ x ∶ A ] B
           → Γ ⊢ₛ₂ N ∶ A
           → Γ ⊢ₛ₂ M · N ∶ B [ x := N ]
      ⊢conv : ∀ {s M A B}
            → Γ ⊢ₛ₂ M ∶ A
            → A ≃β B
            → Γ ⊢ₛ₂ B ∶ c s
            → Γ ⊢ₛ₂ M ∶ B

  validCxt : ∀ {Γ M A} → Γ ⊢ₛ₂ M ∶ A → Γ okₛ₂
  validCxt (⊢sort Γok _) = Γok
  validCxt (⊢prod _ Γ⊢A:s _ _) = validCxt Γ⊢A:s
  validCxt (⊢var Γok _) = Γok    
  validCxt (⊢abs _ _ _ t) = validCxt t
  validCxt (⊢app t _) = validCxt t
  validCxt (⊢conv t _ _) = validCxt t

  -- inversion (generation) lemmas

  genVar : ∀ {Γ x A} → Γ ⊢ₛ₂ v x ∶ A → ∃ λ B → Γ okₛ₂ × (x , B) ∈ Γ × A ≃β B
  genVar {Γ} {x} {A} (⊢var {.x} {.A} Γok x,A∈Γ) = A , Γok , x,A∈Γ , Eq.reflexive (_∼α_ ∪ _→β_)
  genVar {Γ} {x} {A} (⊢conv {_} {.(v x)} {C} {.A} Γ⊢x:C C≃A _) with genVar Γ⊢x:C
  ... | B , Γok , x,B∈Γ , C≃B = B , Γok , x,B∈Γ , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃A) C≃B

  genSort : ∀ {Γ s A} → Γ ⊢ₛ₂ c s ∶ A → ∃ λ t → Γ okₛ₂ × 𝒜 s t × A ≃β c t
  genSort {Γ} {s} {.(c t)} (⊢sort {.s} {t} Γok 𝒜st) = t , Γok , 𝒜st , Eq.reflexive (_∼α_ ∪ _→β_)
  genSort {Γ} {s} {A} (⊢conv {_} {.(c s)} {C} {.A} Γ⊢s:C C≃A _) with genSort Γ⊢s:C
  ... | t , Γok , 𝒜st , C≃t = t , Γok , 𝒜st , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃A) C≃t

  genLam : ∀ {Γ x A M C} → Γ ⊢ₛ₂ λ[ x ∶ A ] M ∶ C
         → ∃₄ λ s x' y B
         → y ∉ fv M - x
         × y ∉ fv B - x'
         × Γ ‚ y ∶ A ⊢ₛ₂ M [ x := v y ] ∶ B [ x' := v y ]
         × Γ ⊢ₛ₂ Π[ x' ∶ A ] B ∶ c s
         × C ≃β Π[ x' ∶ A ] B
  genLam (⊢abs {x} {x'} {y} {s} {A} {B} y∉fvM-x y∉fvB-x' Γ,y:A⊢M[x=y]:B[x'=y] Γ⊢Π[y:A]B:s) =
    s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , Eq.reflexive (_∼α_ ∪ _→β_)
  genLam (⊢conv Γ⊢λ[x:A]M:C C≃D _) with genLam Γ⊢λ[x:A]M:C
  ... |  s ,  x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , D≃Π[x':A]B =
    s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s
    , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃D) D≃Π[x':A]B 

  genAbs = genLam

{-
  genAbsG : ∀ {Γ x A M C} → Γ ⊢ₛ₂ λ[ x ∶ A ] M ∶ C
         → ∀ y → y ∉ dom Γ 
         → ∃₃ λ s x' B 
         → y ∉ fv M - x
         × y ∉ fv B - x'
         × Γ ‚ y ∶ A ⊢ₛ₂ M [ x := v y ] ∶ B [ x' := v y ]
         × Γ ⊢ₛ₂ Π[ x' ∶ A ] B ∶ c s
         × C ≃β Π[ x' ∶ A ] B
  genAbsG {y = y} (⊢abs {x} {x'} {z} {s} {A} {B} y∉fvM-x y∉fvB-x' Γ,y:A⊢M[x=y]:B[x'=y] Γ⊢Π[y:A]B:s) with z ≟ y
  ... | yes _ = ?
  ... | no _ = ?
    -- s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , Eq.reflexive (_∼α_ ∪ _→β_)
  genAbsG (⊢conv Γ⊢λ[x:A]M:C C≃D _) with genLam Γ⊢λ[x:A]M:C
  ... |  s ,  x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , D≃Π[x':A]B =
    s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s
    , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃D) D≃Π[x':A]B
-}

  genProd : ∀ {Γ x A B C} → Γ ⊢ₛ₂ Π[ x ∶ A ] B ∶ C
        → ∃₄ λ s₁ s₂ s₃ y
        → ℛ s₁ s₂ s₃
        × Γ ⊢ₛ₂ A ∶ c s₁
        × y ∉ fv B - x
        × Γ ‚ y ∶ A ⊢ₛ₂ B [ x := v y ] ∶ c s₂
        × C ≃β c s₃
  genProd (⊢prod {x} {y} {s₁} {s₂} {s₃} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , Eq.reflexive (_∼α_ ∪ _→β_)        
  genProd (⊢conv Γ⊢Π[x:A]B:C C=D _) with genProd Γ⊢Π[x:A]B:C
  ... | s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , C=s₃ =
    s₁ , s₂ , s₃ , y , Rs₁s₂s₃ , Γ⊢A:s₁ , y∉fvB-x , Γ,y:A⊢B[x=y]:s₂ , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C=D) C=s₃

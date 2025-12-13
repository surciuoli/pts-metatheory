open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Subset.Propositional
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Binary.Construct.Union

open import Stoughton.Var

module PTS.Equivalence {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  open import PTS isVar 𝒜 ℛ renaming (genProd to genProdInf; freshAsg to freshAsgInf) hiding (validCxt; genLam)
  open import PTS.SyntacticValidity isVar 𝒜 ℛ renaming (syntacticValidity to syntacticValidityInf)
  open import PTS.ClosureSub isVar 𝒜 ℛ using (_∶_⇀_)
    renaming (closureSub to closureSubInf; subUnary to subUnarInf; unaryRen to unaryRenInf; cut to cutInf) public
    
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar
  
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
      ⊢abs : ∀ {x y z s A B M}
           → z ∉ fv M - x
           → z ∉ fv B - y
           → Γ ‚ z ∶ A ⊢ₛ M [ x := v z ] ∶ B [ y := v z ]
           → Γ ⊢ₛ Π[ y ∶ A ] B ∶ c s
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
  validCxt (⊢abs _ _ _ t) = validCxt t
  validCxt (⊢app t _) = validCxt t
  validCxt (⊢conv t _ _) = validCxt t

  -- inversion (generation) lemmas

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

  genLam : ∀ {Γ x A M C} → Γ ⊢ₛ λ[ x ∶ A ] M ∶ C
         → ∃₄ λ s x' y B
         → y ∉ fv M - x
         × y ∉ fv B - x'
         × Γ ‚ y ∶ A ⊢ₛ M [ x := v y ] ∶ B [ x' := v y ]
         × Γ ⊢ₛ Π[ x' ∶ A ] B ∶ c s
         × C ≃β Π[ x' ∶ A ] B
  genLam (⊢abs {x} {x'} {y} {s} {A} {B} y∉fvM-x y∉fvB-x' Γ,y:A⊢M[x=y]:B[x'=y] Γ⊢Π[y:A]B:s) =
    s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , Eq.reflexive (_∼α_ ∪ _→β_)
  genLam (⊢conv Γ⊢λ[x:A]M:C C≃D _) with genLam Γ⊢λ[x:A]M:C
  ... |  s ,  x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s , D≃Π[x':A]B =
    s , x' , y , B , y∉fvM-x , y∉fvB-x' , Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[y:A]B:s
    , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃D) D≃Π[x':A]B 
    
  eqJudgCxt→ : ∀ {Γ} → Γ ok → Γ okₛ
  eqJudgAsg→ : ∀ {Γ M A} → Γ ⊢ M ∶ A → Γ ⊢ₛ M ∶ A

  eqJudgCxt→ ⊢nil = ⊢nil
  eqJudgCxt→ (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (eqJudgCxt→ Γok) x∉Γ (eqJudgAsg→ Γ⊢A:s)

  eqJudgAsg→ (⊢sort Γok As₁s₂) = ⊢sort (eqJudgCxt→ Γok) As₁s₂
  eqJudgAsg→ (⊢var Γok x,A∈Γ) = ⊢var (eqJudgCxt→ Γok) x,A∈Γ
  eqJudgAsg→ {Γ} Γ⊢Π[x:A]B:s₃@(⊢prod {x} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ ∀y→Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (eqJudgAsg→ Γ⊢A:s₁) y∉fvB-x (eqJudgAsg→ (∀y→Γ,y:A⊢B[x=y]:s₂ y y∉domΓ))
    where
    y : 𝒱
    y = X' (dom Γ)
    y∉domΓ : y ∉ dom Γ
    y∉domΓ = Xpfresh (dom Γ)
    y∉fvB-x : y ∉ fv B - x
    y∉fvB-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsgInf y∉domΓ Γ⊢Π[x:A]B:s₃))
  eqJudgAsg→ {Γ} Γ⊢λ[x:A]M:Π[y:A]B@(⊢abs {x} {y} {s} {A} {B} {M} ∀z→Γ,z:A⊢M[x=z]:B[y=z] Γ⊢Π[y:A]B:s) =
    ⊢abs
        z∉fvM-x
        z∉fvB-y
        (eqJudgAsg→ (∀z→Γ,z:A⊢M[x=z]:B[y=z] z z∉domΓ))
        (eqJudgAsg→ Γ⊢Π[y:A]B:s)
    where
    z : 𝒱
    z = X' (dom Γ)
    z∉domΓ : z ∉ dom Γ
    z∉domΓ = Xpfresh (dom Γ)
    z∉fvM-x : z ∉ fv M - x
    z∉fvM-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsgInf z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
    z∉fvB-y : z ∉ fv B - y
    z∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉ys {xs = fv (λ[ x ∶ A ] M)} (freshAsgInf z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
  eqJudgAsg→ (⊢app Γ⊢M:Π[x:A]B Γ⊢N:A _) = ⊢app (eqJudgAsg→ Γ⊢M:Π[x:A]B) (eqJudgAsg→ Γ⊢N:A)
  eqJudgAsg→ (⊢conv Γ⊢M:A A=B Γ⊢B:s) = ⊢conv (eqJudgAsg→ Γ⊢M:A) A=B (eqJudgAsg→ Γ⊢B:s)
  
  eqJudgCxt← : ∀ {Γ} → Γ okₛ → Γ ok
  eqJudgAsg← : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → Γ ⊢ M ∶ A

  eqJudgCxt← ⊢nil = ⊢nil
  eqJudgCxt← (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (eqJudgCxt← Γok) x∉Γ (eqJudgAsg← Γ⊢A:s)

  eqJudgAsg← (⊢sort Γok As₁s₂) = ⊢sort (eqJudgCxt← Γok) As₁s₂
  eqJudgAsg← (⊢var Γok x,A∈Γ) = ⊢var (eqJudgCxt← Γok) x,A∈Γ
  eqJudgAsg← {Γ} (⊢prod {x} {y} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (eqJudgAsg← Γ⊢A:s₁) goal
    where
    goal : ∀ y' → y' ∉ dom Γ → Γ ‚ y' ∶ A ⊢ B [ x := v y' ] ∶ c s₂
    goal y' y'∉domΓ = Γ‚y':A⊢B[x=y']:s₂
      where
      Γ‚y:A⊢B[x=y]:s₂ : Γ ‚ y ∶ A ⊢ B [ x := v y ] ∶ c s₂
      Γ‚y:A⊢B[x=y]:s₂ = eqJudgAsg← Γ,y:A⊢B[x=y]:s₂
      Γ‚y':A⊢B[x=y][y=y']:s₂ : Γ ‚ y' ∶ A ⊢ B [ x := v y ] [ y := v y' ] ∶ c s₂
      Γ‚y':A⊢B[x=y][y=y']:s₂ = unaryRenInf y'∉domΓ Γ‚y:A⊢B[x=y]:s₂ 
      Γ‚y':A⊢B[x=y']:s₂ : Γ ‚ y' ∶ A ⊢ B [ x := v y' ] ∶ c s₂
      Γ‚y':A⊢B[x=y']:s₂ = subst (λ C → Γ ‚ y' ∶ A ⊢ C ∶ c s₂) (sym (composRenUpd {x} {y} {B} y∉fvB-x)) Γ‚y':A⊢B[x=y][y=y']:s₂   
  eqJudgAsg← {Γ} h@(⊢abs {x} {y} {z} {s} {A} {B} {M} z∉fvM-x z∉fvB-y Γ,z:A⊢M[x=z]:B[y=z] Γ⊢Π[x:A]B:s) =
    ⊢abs goal2 (eqJudgAsg← Γ⊢Π[x:A]B:s)
    where
    goal2 : ∀ z' → z' ∉ dom Γ → Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
    goal2 z' z'∉domΓ = Γ‚z':A⊢M[x=z']:B[y=z']
      where
      Γ‚z:A⊢M[x=z]:B[y=z] : Γ ‚ z ∶ A ⊢ M [ x := v z ] ∶ B [ y := v z ] 
      Γ‚z:A⊢M[x=z]:B[y=z] = eqJudgAsg← Γ,z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z ] [ z := v z' ] ∶ B [ y := v z ] [ z := v z' ] 
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] = unaryRenInf z'∉domΓ Γ‚z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z']:B[y=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
      Γ‚z':A⊢M[x=z']:B[y=z'] =
        subst₂
          (λ N C → Γ ‚ z' ∶ A ⊢ N ∶ C)
          (sym (composRenUpd {x} {z} {M} z∉fvM-x))
          (sym (composRenUpd {y} {z} {B} z∉fvB-y))
          Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z']
      
  eqJudgAsg← {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛM:Π[x:A]B Γ⊢ₛN:A) with syntacticValidityInf Γ⊢M:Π[x:A]B
    where
    Γ⊢M:Π[x:A]B : Γ ⊢ M ∶ Π[ x ∶ A ] B 
    Γ⊢M:Π[x:A]B = eqJudgAsg← Γ⊢ₛM:Π[x:A]B    
  eqJudgAsg← _ | _ , inj₁ ()
  eqJudgAsg← {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛM:Π[x:A]B Γ⊢ₛN:A) | s , inj₂ Γ⊢Π[x:A]B:s =
    ⊢app Γ⊢M:Π[x:A]B Γ⊢N:A (proj₂ Γ⊢B[x=N]:s)
    where
    Γ⊢M:Π[x:A]B : Γ ⊢ M ∶ Π[ x ∶ A ] B 
    Γ⊢M:Π[x:A]B = eqJudgAsg← Γ⊢ₛM:Π[x:A]B        
    Γ⊢N:A : Γ ⊢ N ∶ A
    Γ⊢N:A = eqJudgAsg← Γ⊢ₛN:A
    z : 𝒱
    z = X' (dom Γ)
    z∉Γ : z ∉ dom Γ
    z∉Γ = Xpfresh (dom Γ)
    Γ,z:A⊢B[x=z]:s : ∃ λ s → Γ ‚ z ∶ A ⊢ B [ x := v z ] ∶ c s
    Γ,z:A⊢B[x=z]:s with genProdInf Γ⊢Π[x:A]B:s
    ... | _ , s , _ , _ , _ , h , _ = s , h z z∉Γ 
    z∉fvB-x : z ∉ fv B - x
    z∉fvB-x = c∉xs++ys→c∉ys (c∉xs++ys→c∉ys {xs = fv M} (freshAsgInf z∉Γ Γ⊢M:Π[x:A]B))
    B[x=z][z=N]=B[x=N] : B [ x := v z ] [ z := N ] ≡ B [ x := N ]
    B[x=z][z=N]=B[x=N] = sym (composRenUpd {x} {z} {B} {N} z∉fvB-x)
    Γ⊢B[x=N]:s : ∃ λ s → Γ ⊢ B [ x := N ] ∶ c s
    Γ⊢B[x=N]:s = s' , subst (λ X → Γ ⊢ X ∶ c s') B[x=z][z=N]=B[x=N] (cutInf (proj₂ Γ,z:A⊢B[x=z]:s) Γ⊢N:A)
      where
      s' : 𝒞
      s' = proj₁ Γ,z:A⊢B[x=z]:s
  eqJudgAsg← (⊢conv Γ⊢M:A A=B Γ⊢B:s) =
    ⊢conv (eqJudgAsg← Γ⊢M:A) A=B (eqJudgAsg← Γ⊢B:s)
  
  eqJudgCxt : ∀ {Γ} → Γ ok ↔ Γ okₛ
  eqJudgAsg : ∀ {Γ M A} → Γ ⊢ M ∶ A ↔ Γ ⊢ₛ M ∶ A 
 
  eqJudgCxt = eqJudgCxt→ , eqJudgCxt←
  eqJudgAsg = eqJudgAsg→ , eqJudgAsg← 

  module _ where
  
    open import PTS.Thinning isVar 𝒜 ℛ renaming (thinning to thinningInf)
    open import PTS.ClosureAlpha isVar 𝒜 ℛ using (_≈α_; ∼ρs)
      renaming (closureAlpha to closureAlphaInf) public

    thinning : ∀ {Γ Δ M A} →  Γ ⊆ Δ → Δ okₛ → Γ ⊢ₛ M ∶ A → Δ ⊢ₛ M ∶ A
    thinning Γ⊆Δ Δok 𝒟 = eqJudgAsg→ (thinningInf Γ⊆Δ (eqJudgCxt← Δok) (eqJudgAsg← 𝒟))

    closureAlpha : ∀ {Γ Δ M N A B} → Γ ≈α Δ → M ∼α N → A ∼α B → Γ ⊢ₛ M ∶ A → Δ ⊢ₛ N ∶ B
    closureAlpha Γ∼Δ M∼N A∼B 𝒟 = eqJudgAsg→ (closureAlphaInf Γ∼Δ M∼N A∼B (eqJudgAsg← 𝒟))

--    closureSub : ∀ {σ Γ Δ M A} → Γ ⊢ₛ M ∶ A → σ ∶ Γ ⇀ Δ → Δ okₛ → Δ ⊢ₛ M ∙ σ ∶ A ∙ σ
--    closureSub 𝒟 𝓈 ℰ = eqJudgAsg→ (closureSubInf 𝓈 (eqJudgCxt← ℰ) (eqJudgAsg← 𝒟))

    cut :  ∀ {Γ M N A B x} → Γ ‚ x ∶ A ⊢ₛ M ∶ B → Γ ⊢ₛ N ∶ A → Γ ⊢ₛ M [ x := N ] ∶ B [ x := N ]
    cut 𝒟 ℰ = eqJudgAsg→ (cutInf (eqJudgAsg← 𝒟) (eqJudgAsg← ℰ))

    syntacticValidity : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → ∃ λ s → A ≡ c s ⊎ Γ ⊢ₛ A ∶ c s
    syntacticValidity 𝒟 with syntacticValidityInf (eqJudgAsg← 𝒟)
    ... | s , ℰ = s , Data.Sum.map (λ x → x) eqJudgAsg→ ℰ

    freshAsg : ∀ {Γ M A w} → w ∉ dom Γ → Γ ⊢ₛ M ∶ A → w # M · A
    freshAsg w∉domΓ 𝒟 = freshAsgInf w∉domΓ (eqJudgAsg← 𝒟)

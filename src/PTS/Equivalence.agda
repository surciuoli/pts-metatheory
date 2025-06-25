open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
  
open import Stoughton.Var

module PTS.Equivalence {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  open import PTS isVar 𝒜 ℛ
  open import PTS.SyntacticValidity isVar 𝒜 ℛ
  open import PTS.ClosureSub isVar 𝒜 ℛ
  
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  
  infix 3 _okₛ 
  infix 3 _⊢ₛ_∶_ 

  data _okₛ : Cxt → Set 
  data _⊢ₛ_∶_ Cxt : Λ → Λ → Set 
  
  data _okₛ where 
    ⊢nil : [] okₛ 
    ⊢cons : ∀ {Γ x s A}
          → Γ okₛ
          → x ∉ dom Γ
          → Γ ⊢ₛ A ∶ c s
          → Γ ‚ x ∶ A okₛ 

  data _⊢ₛ_∶_ Γ where 
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
         → Γ ⊢ₛ A ∶ c s₁
         → z ∉ fv M - x
         → z ∉ fv B - y
         → Γ ‚ z ∶ A ⊢ₛ B [ y := v z ] ∶ c s₂
         → Γ ‚ z ∶ A ⊢ₛ M [ x := v z ] ∶ B [ y := v z ]
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
    y∉fvB-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsg y∉domΓ Γ⊢Π[x:A]B:s₃))
  eqJudgAsg→ {Γ} Γ⊢λ[x:A]M:Π[y:A]B@(⊢abs {x} {y} {s₁} {s₂} {s₃} {A} {B} {M} Rs₁s₂s₃ Γ⊢A:s₁ ∀z→Γ,z:A⊢B[y=z]:s₂ ∀z→Γ,z:A⊢M[x=z]:B[y=z]) =
    ⊢abs Rs₁s₂s₃ (eqJudgAsg→ Γ⊢A:s₁) z∉fvM-x z∉fvB-y (eqJudgAsg→ (∀z→Γ,z:A⊢B[y=z]:s₂ z z∉domΓ)) (eqJudgAsg→ (∀z→Γ,z:A⊢M[x=z]:B[y=z] z z∉domΓ))
    where
    z : 𝒱
    z = X' (dom Γ)
    z∉domΓ : z ∉ dom Γ
    z∉domΓ = Xpfresh (dom Γ)
    z∉fvM-x : z ∉ fv M - x
    z∉fvM-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsg z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
    z∉fvB-y : z ∉ fv B - y
    z∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉ys {xs = fv (λ[ x ∶ A ] M)} (freshAsg z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
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
      Γ‚y':A⊢B[x=y][y=y']:s₂ = unaryRen y'∉domΓ Γ‚y:A⊢B[x=y]:s₂ 
      Γ‚y':A⊢B[x=y']:s₂ : Γ ‚ y' ∶ A ⊢ B [ x := v y' ] ∶ c s₂
      Γ‚y':A⊢B[x=y']:s₂ = subst (λ C → Γ ‚ y' ∶ A ⊢ C ∶ c s₂) (sym (composRenUpd {x} {y} {B} y∉fvB-x)) Γ‚y':A⊢B[x=y][y=y']:s₂   
  eqJudgAsg← {Γ} (⊢abs {x} {y} {z} {s₁} {s₂} {s₃} {A} {B} {M} Rs₁s₂s₃ Γ⊢A:s₁ z∉fvM-x z∉fvB-y Γ,z:A⊢B[y=z]:s₂ Γ,z:A⊢M[x=z]:B[y=z]) =
    ⊢abs Rs₁s₂s₃ (eqJudgAsg← Γ⊢A:s₁) goal goal2
    where
    goal : ∀ z' → z' ∉ dom Γ → Γ ‚ z' ∶ A ⊢ B [ y := v z' ] ∶ c s₂
    goal z' z'∉domΓ = Γ‚z':A⊢B[y=z']:s₂
      where
      Γ‚z:A⊢B[y=z]:s₂ : Γ ‚ z ∶ A ⊢ B [ y := v z ] ∶ c s₂
      Γ‚z:A⊢B[y=z]:s₂ = eqJudgAsg← Γ,z:A⊢B[y=z]:s₂
      Γ‚z':A⊢B[y=z][z=z']:s₂ : Γ ‚ z' ∶ A ⊢ B [ y := v z ] [ z := v z' ] ∶ c s₂
      Γ‚z':A⊢B[y=z][z=z']:s₂ = unaryRen z'∉domΓ Γ‚z:A⊢B[y=z]:s₂ 
      Γ‚z':A⊢B[y=z']:s₂ : Γ ‚ z' ∶ A ⊢ B [ y := v z' ] ∶ c s₂
      Γ‚z':A⊢B[y=z']:s₂ = subst (λ C → Γ ‚ z' ∶ A ⊢ C ∶ c s₂) (sym (composRenUpd {y} {z} {B} z∉fvB-y)) Γ‚z':A⊢B[y=z][z=z']:s₂
    goal2 : ∀ z' → z' ∉ dom Γ → Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
    goal2 z' z'∉domΓ = Γ‚z':A⊢M[x=z']:B[y=z']
      where
      Γ‚z:A⊢M[x=z]:B[y=z] : Γ ‚ z ∶ A ⊢ M [ x := v z ] ∶ B [ y := v z ] 
      Γ‚z:A⊢M[x=z]:B[y=z] = eqJudgAsg← Γ,z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z ] [ z := v z' ] ∶ B [ y := v z ] [ z := v z' ] 
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] = unaryRen z'∉domΓ Γ‚z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z']:B[y=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
      Γ‚z':A⊢M[x=z']:B[y=z'] =
        subst₂
          (λ N C → Γ ‚ z' ∶ A ⊢ N ∶ C)
          (sym (composRenUpd {x} {z} {M} z∉fvM-x))
          (sym (composRenUpd {y} {z} {B} z∉fvB-y))
          Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z']
  eqJudgAsg← {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛM:Π[x:A]B Γ⊢ₛN:A) with syntacticValidity Γ⊢M:Π[x:A]B
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
    Γ,z:A⊢B[x=z]:s with genProd Γ⊢Π[x:A]B:s
    ... | _ , s , _ , _ , _ , h , _ = s , h z z∉Γ 
    z∉fvB-x : z ∉ fv B - x
    z∉fvB-x = c∉xs++ys→c∉ys (c∉xs++ys→c∉ys {xs = fv M} (freshAsg z∉Γ Γ⊢M:Π[x:A]B))
    B[x=z][z=N]=B[x=N] : B [ x := v z ] [ z := N ] ≡ B [ x := N ]
    B[x=z][z=N]=B[x=N] = sym (composRenUpd {x} {z} {B} {N} z∉fvB-x)
    Γ⊢B[x=N]:s : ∃ λ s → Γ ⊢ B [ x := N ] ∶ c s
    Γ⊢B[x=N]:s = s' , subst (λ X → Γ ⊢ X ∶ c s') B[x=z][z=N]=B[x=N] (cut (proj₂ Γ,z:A⊢B[x=z]:s) Γ⊢N:A)
      where
      s' : 𝒞
      s' = proj₁ Γ,z:A⊢B[x=z]:s
  eqJudgAsg← (⊢conv Γ⊢M:A A=B Γ⊢B:s) =
    ⊢conv (eqJudgAsg← Γ⊢M:A) A=B (eqJudgAsg← Γ⊢B:s)
  
  eqJudgCxt : ∀ {Γ} → Γ ok ↔ Γ okₛ
  eqJudgAsg : ∀ {Γ M A} → Γ ⊢ M ∶ A ↔ Γ ⊢ₛ M ∶ A 
 
  eqJudgCxt = eqJudgCxt→ , eqJudgCxt←
  eqJudgAsg = eqJudgAsg→ , eqJudgAsg← 
